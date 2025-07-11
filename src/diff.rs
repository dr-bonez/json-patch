use std::collections::BTreeSet;

use imbl_value::Value;
use json_ptr::JsonPointer;

use crate::{AddOperation, PatchOperation, RemoveOperation, ReplaceOperation};

struct PatchDiffer {
    path: JsonPointer,
    patch: super::Patch,
}

impl PatchDiffer {
    fn new() -> Self {
        Self {
            path: JsonPointer::default(),
            patch: super::Patch(Vec::new()),
        }
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
pub fn diff(from: &Value, to: &Value) -> super::Patch {
    let mut differ = PatchDiffer::new();
    diff_mut(&mut differ, from, to);
    differ.patch
}

fn diff_mut(differ: &mut PatchDiffer, from: &Value, to: &Value) {
    match (from, to) {
        (Value::Object(f), Value::Object(t)) if !f.ptr_eq(t) => {
            for key in f
                .keys()
                .chain(t.keys())
                .map(|k| &**k)
                .collect::<BTreeSet<_>>()
            {
                differ.path.push_end(key);
                match (f.get(key), to.get(key)) {
                    (Some(f), Some(t)) if f != t => {
                        diff_mut(differ, f, t);
                    }
                    (Some(_), None) => {
                        differ.patch.0.push(PatchOperation::Remove(RemoveOperation {
                            path: differ.path.clone(),
                        }));
                    }
                    (None, Some(t)) => {
                        differ.patch.0.push(PatchOperation::Add(AddOperation {
                            path: differ.path.clone(),
                            value: t.clone(),
                        }));
                    }
                    _ => (),
                }
                differ.path.pop_end();
            }
        }
        (Value::Array(f), Value::Array(t)) if !f.ptr_eq(t) => {
            if f.len() < t.len() {
                let mut f_idx = 0;
                let mut t_idx = 0;
                while t_idx < t.len() {
                    if f_idx == f.len() {
                        differ.patch.0.push(PatchOperation::Add(AddOperation {
                            path: differ.path.clone().join_end_idx(t_idx),
                            value: t[t_idx].clone(),
                        }));
                        t_idx += 1;
                    } else {
                        if !f[f_idx].ptr_eq(&t[t_idx]) {
                            if t.iter().skip(t_idx + 1).any(|t| f[f_idx].ptr_eq(t)) {
                                differ.patch.0.push(PatchOperation::Add(AddOperation {
                                    path: differ.path.clone().join_end_idx(t_idx),
                                    value: t[t_idx].clone(),
                                }));
                                t_idx += 1;
                                continue;
                            } else {
                                differ.path.push_end_idx(t_idx);
                                diff_mut(differ, &f[f_idx], &t[t_idx]);
                                differ.path.pop_end();
                            }
                        }
                        f_idx += 1;
                        t_idx += 1;
                    }
                }
            } else if f.len() > t.len() {
                let mut f_idx = 0;
                let mut t_idx = 0;
                while f_idx < f.len() {
                    if t_idx == t.len() {
                        differ.patch.0.push(PatchOperation::Remove(RemoveOperation {
                            path: differ.path.clone().join_end_idx(t_idx),
                        }));
                        f_idx += 1;
                    } else {
                        if !f[f_idx].ptr_eq(&t[t_idx]) {
                            if f.iter().skip(f_idx + 1).any(|f| t[t_idx].ptr_eq(f)) {
                                differ.patch.0.push(PatchOperation::Remove(RemoveOperation {
                                    path: differ.path.clone().join_end_idx(t_idx),
                                }));
                                f_idx += 1;
                                continue;
                            } else {
                                differ.path.push_end_idx(t_idx);
                                diff_mut(differ, &f[f_idx], &t[t_idx]);
                                differ.path.pop_end();
                            }
                        }
                        f_idx += 1;
                        t_idx += 1;
                    }
                }
            } else {
                for i in 0..f.len() {
                    if !f[i].ptr_eq(&t[i]) {
                        differ.path.push_end_idx(i);
                        diff_mut(differ, &f[i], &t[i]);
                        differ.path.pop_end();
                    }
                }
            }
        }
        (f, t) if f != t => differ
            .patch
            .0
            .push(PatchOperation::Replace(ReplaceOperation {
                path: differ.path.clone(),
                value: t.clone(),
            })),
        _ => (),
    }
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
                { "op": "replace", "path": "", "value": &right },
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
