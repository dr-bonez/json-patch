use imbl_value::Value;
use json_ptr::JsonPointer;

struct PatchDiffer {
    path: JsonPointer,
    patch: super::Patch,
    shift: usize,
}

impl PatchDiffer {
    fn new() -> Self {
        Self {
            path: "".parse().unwrap(),
            patch: super::Patch(Vec::new()),
            shift: 0,
        }
    }
}

impl<'a> treediff::Delegate<'a, imbl_value::treediff::Key, Value> for PatchDiffer {
    fn push(&mut self, key: &imbl_value::treediff::Key) {
        match *key {
            imbl_value::treediff::Key::Index(idx) => self.path.push_end_idx(idx - self.shift),
            imbl_value::treediff::Key::String(ref key) => self.path.push_end(key),
        }
    }

    fn pop(&mut self) {
        self.path.pop_end();
        self.shift = 0;
    }

    fn removed<'b>(&mut self, k: &'b imbl_value::treediff::Key, _v: &'a Value) {
        let len = self.path.len();
        self.push(k);
        self.patch
            .0
            .push(super::PatchOperation::Remove(super::RemoveOperation {
                path: self.path.clone(),
            }));
        // Shift indices, we are deleting array elements
        if let imbl_value::treediff::Key::Index(_) = k {
            self.shift += 1;
        }
        self.path.truncate(len);
    }

    fn added(&mut self, k: &imbl_value::treediff::Key, v: &Value) {
        let len = self.path.len();
        self.push(k);
        self.patch
            .0
            .push(super::PatchOperation::Add(super::AddOperation {
                path: self.path.clone(),
                value: v.clone(),
            }));
        self.path.truncate(len);
    }

    fn modified(&mut self, _old: &'a Value, new: &'a Value) {
        self.patch
            .0
            .push(super::PatchOperation::Replace(super::ReplaceOperation {
                path: self.path.clone(),
                value: new.clone(),
            }));
    }
}

/// Diff two JSON documents and generate a JSON Patch (RFC 6902).
///
/// # Example
/// Diff two JSONs:
///
/// ```rust
/// #[macro_use]
/// extern crate imbl_value;
/// extern crate json_patch;
///
/// use json_patch::{patch, diff, from_value};
///
/// # pub fn main() {
/// let left = json!({
///   "title": "Goodbye!",
///   "author" : {
///     "givenName" : "John",
///     "familyName" : "Doe"
///   },
///   "tags":[ "example", "sample" ],
///   "content": "This will be unchanged"
/// });
///
/// let right = json!({
///   "title": "Hello!",
///   "author" : {
///     "givenName" : "John"
///   },
///   "tags": [ "example" ],
///   "content": "This will be unchanged",
///   "phoneNumber": "+01-123-456-7890"
/// });
///
/// let p = diff(&left, &right);
/// assert_eq!(p, from_value(json!([
///   { "op": "remove", "path": "/author/familyName" },
///   { "op": "remove", "path": "/tags/1" },
///   { "op": "replace", "path": "/title", "value": "Hello!" },
///   { "op": "add", "path": "/phoneNumber", "value": "+01-123-456-7890" },
/// ])).unwrap());
///
/// let mut doc = left.clone();
/// patch(&mut doc, &p).unwrap();
/// assert_eq!(doc, right);
///
/// # }
/// ```
pub fn diff(left: &Value, right: &Value) -> super::Patch {
    let mut differ = PatchDiffer::new();
    treediff::diff(left, right, &mut differ);
    differ.patch
}

#[cfg(test)]
mod tests {
    use imbl_value::Value;

    #[test]
    pub fn replace_all() {
        let left = json!({"title": "Hello!"});
        let p = super::diff(&left, &Value::Null);
        assert_eq!(
            p,
            imbl_value::from_value(json!([
                { "op": "replace", "path": "", "value": null },
            ]))
            .unwrap()
        );
    }

    #[test]
    pub fn add_all() {
        let right = json!({"title": "Hello!"});
        let p = super::diff(&Value::Null, &right);
        assert_eq!(
            p,
            imbl_value::from_value(json!([
                { "op": "replace", "path": "", "value": { "title": "Hello!" } },
            ]))
            .unwrap()
        );
    }

    #[test]
    pub fn remove_all() {
        let left = json!(["hello", "bye"]);
        let right = json!([]);
        let p = super::diff(&left, &right);
        assert_eq!(
            p,
            imbl_value::from_value(json!([
                { "op": "remove", "path": "/0" },
                { "op": "remove", "path": "/0" },
            ]))
            .unwrap()
        );
    }

    #[test]
    pub fn remove_tail() {
        let left = json!(["hello", "bye", "hi"]);
        let right = json!(["hello"]);
        let p = super::diff(&left, &right);
        assert_eq!(
            p,
            imbl_value::from_value(json!([
                { "op": "remove", "path": "/1" },
                { "op": "remove", "path": "/1" },
            ]))
            .unwrap()
        );
    }
    #[test]
    pub fn replace_object() {
        let left = json!(["hello", "bye"]);
        let right = json!({"hello": "bye"});
        let p = super::diff(&left, &right);
        assert_eq!(
            p,
            imbl_value::from_value(json!([
                { "op": "add", "path": "/hello", "value": "bye" },
                { "op": "remove", "path": "/0" },
                { "op": "remove", "path": "/0" },
            ]))
            .unwrap()
        );
    }

    #[test]
    fn escape_json_keys() {
        let mut left = json!({
            "/slashed/path": 1
        });
        let right = json!({
            "/slashed/path": 2,
        });
        let patch = super::diff(&left, &right);

        eprintln!("{:?}", patch);

        crate::patch(&mut left, &patch).unwrap();
        assert_eq!(left, right);
    }
}
