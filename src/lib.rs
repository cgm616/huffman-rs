use std::rc::Rc;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

#[derive(Clone, Eq, PartialEq)]
struct FreqNode<T> {
    freq: usize,
    node: TreePath<T>,
}

#[derive(Debug)]
pub struct HuffmanTree<T> {
    dict: ElemDict<T>,
    head: TreePath<T>,
}

type ElemDict<T> = BTreeMap<T, Rc<RefCell<LeafNode<T>>>>;

type TreePath<T> = Option<Type<T>>;

#[derive(Clone, Eq, PartialEq, Debug)]
enum Type<T> {
    Branch(Rc<RefCell<BranchNode<T>>>),
    Leaf(Rc<RefCell<LeafNode<T>>>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
enum Side {
    Left,
    Right,
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct LeafNode<T> {
    elem: T,
    side: Option<Side>,
    parent: TreePath<T>,
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct BranchNode<T> {
    side: Option<Side>,
    parent: TreePath<T>,
    left: TreePath<T>,
    right: TreePath<T>,
}

impl<T> Ord for FreqNode<T> where T: std::cmp::Eq {
    fn cmp(&self, other: &FreqNode<T>) -> Ordering {
        other.freq.cmp(&self.freq)
    }
}

impl<T> PartialOrd for FreqNode<T> where T: std::cmp::PartialEq, T: std::cmp::Eq {
    fn partial_cmp(&self, other: &FreqNode<T>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> HuffmanTree<T> where T: std::cmp::Ord, T: std::clone::Clone, T: std::marker::Copy {
    fn new() -> Self {
        HuffmanTree { dict: BTreeMap::new(), head: None }
    }

    fn build(&mut self, sequence: &[T]) {
        let mut freq_counter: BTreeMap<T, usize> = BTreeMap::new();

        for elem in sequence {
            *freq_counter.entry(*elem).or_insert(0) += 1;
        }

        let mut queue: BinaryHeap<FreqNode<T>> = BinaryHeap::new();

        let mut dict: ElemDict<T> = BTreeMap::new();

        for (elem, freq) in freq_counter {
            let boxed_leaf = Rc::new(RefCell::new(LeafNode { elem: elem, side: None, parent: None }));
            let node = Some(Type::Leaf(boxed_leaf));
            queue.push(FreqNode { freq: freq, node: node });
        }

        while let Some(left_node) = queue.pop() {
            if let Some(right_node) = queue.pop() {
                let freq = left_node.freq + right_node.freq;

                let mut left_node = left_node.node;
                let mut right_node = right_node.node;

                let new_node = Rc::new(RefCell::new(BranchNode { side: None,
                                                parent: None,
                                                left: None,
                                                right: None }));

                match left_node.as_mut() {
                    Some(&mut Type::Branch(ref mut unwrapped_left_node)) => {
                        unwrapped_left_node.borrow_mut().parent = Some(Type::Branch(new_node.clone()));
                        unwrapped_left_node.borrow_mut().side = Some(Side::Left);
                    },
                    Some(&mut Type::Leaf(ref mut unwrapped_left_node)) => {
                        unwrapped_left_node.borrow_mut().parent = Some(Type::Branch(new_node.clone()));
                        unwrapped_left_node.borrow_mut().side = Some(Side::Left);
                        dict.insert(unwrapped_left_node.borrow().elem, unwrapped_left_node.clone());
                    },
                    None => {},
                }

                match right_node.as_mut() {
                    Some(&mut Type::Branch(ref mut unwrapped_right_node)) => {
                        unwrapped_right_node.borrow_mut().parent = Some(Type::Branch(new_node.clone()));
                        unwrapped_right_node.borrow_mut().side = Some(Side::Right);
                    },
                    Some(&mut Type::Leaf(ref mut unwrapped_right_node)) => {
                        unwrapped_right_node.borrow_mut().parent = Some(Type::Branch(new_node.clone()));
                        unwrapped_right_node.borrow_mut().side = Some(Side::Right);
                        dict.insert(unwrapped_right_node.borrow().elem, unwrapped_right_node.clone());
                    },
                    None => {},
                }

                new_node.borrow_mut().left = left_node;
                new_node.borrow_mut().right = right_node;

                let new_node = Some(Type::Branch(new_node));
                queue.push(FreqNode { freq: freq, node: new_node });
            } else {
                self.head = left_node.node;
            }
        }

        self.dict = dict;
    }
}

fn walk_up_nodes<T>(node: &TreePath<T>, buffer: &mut Vec<u8>) {
    if let Some(Type::Branch(ref node)) = *node {
        match node.borrow().side {
            Some(Side::Left) => {
                buffer.push(0);
            },
            Some(Side::Right) => {
                buffer.push(1);
            },
            None => {},
        }

        walk_up_nodes(&node.borrow().parent, buffer);
    }
}

pub fn encode<T>(tree: &HuffmanTree<T>, sequence: &[T]) -> Vec<u8> where T: std::cmp::Ord {
    let mut output: Vec<u8> = Vec::new();

    for elem in sequence {
        let mut char_buffer: Vec<u8> = Vec::new();

        match tree.dict.get(elem) {
            Some(leaf) => {
                match leaf.borrow().side {
                    Some(Side::Left) => {
                        char_buffer.push(0);
                    },
                    Some(Side::Right) => {
                        char_buffer.push(1);
                    },
                    None => {},
                }

                walk_up_nodes(&leaf.borrow().parent, &mut char_buffer);
            },
            None => panic!("Element in input not encoded in tree"),
        }

        char_buffer.reverse();
        output.append(&mut char_buffer);
    }

    output
}

fn walk_down_nodes<T>(head: &TreePath<T>, node: &TreePath<T>, mut buffer: &mut Vec<T>, input: &[u8]) where T: std::marker::Copy {
    match *node {
        Some(Type::Branch(ref node)) => {
            match input[0] {
                1 => {
                    match input.len() {
                        1 => {
                            let ref new_node = node.borrow().right;
                            if let &Some(Type::Leaf(ref node)) = new_node {
                                buffer.push(node.borrow().elem);
                            }
                        },
                        _ => walk_down_nodes(head, &node.borrow().right, &mut buffer, &input[1..]),
                    }
                },
                0 => {
                    match input.len() {
                        1 => {
                            let ref new_node = node.borrow().left;
                            if let &Some(Type::Leaf(ref node)) = new_node {
                                buffer.push(node.borrow().elem);
                            }
                        },
                        _ => walk_down_nodes(head, &node.borrow().left, &mut buffer, &input[1..]),
                    }
                },
                _ => panic!("Bit stream is not only zeroes or ones"),
            }
        },
        Some(Type::Leaf(ref node)) => {
            buffer.push(node.borrow().elem);
            walk_down_nodes(head, head, &mut buffer, input);
        },
        None => {},
    }
}

pub fn decode<T>(tree: &HuffmanTree<T>, bit_stream: &[u8]) -> Vec<T> where T: std::marker::Copy {
    let mut output: Vec<T> = Vec::new();
    if bit_stream.len() > 0 {
        walk_down_nodes(&tree.head, &tree.head, &mut output, bit_stream);
    }

    output
}

#[cfg(test)]
mod test {
    use std::str;
    use super::HuffmanTree;
    #[test]
    fn basics() {
        let mut tree = HuffmanTree::new();
        let sentence = "Today, I walked over the Brooklyn Bridge.";
        tree.build(sentence.as_bytes());

        assert!(tree.dict.contains_key("T".as_bytes().first().unwrap()));
        assert!(tree.dict.contains_key(".".as_bytes().first().unwrap()));
        assert!(tree.dict.contains_key("o".as_bytes().first().unwrap()));

        assert!(!tree.dict.contains_key("u".as_bytes().first().unwrap()));
        assert!(!tree.dict.contains_key("3".as_bytes().first().unwrap()));
        assert!(!tree.dict.contains_key("b".as_bytes().first().unwrap()));
    }

    #[test]
    fn encode() {
        let mut tree = HuffmanTree::new();
        let dictionary = "AAAABBBCCD";
        tree.build(dictionary.as_bytes());

        assert_eq!(super::encode(&tree, "A".as_bytes()), vec![0]);
        assert_eq!(super::encode(&tree, "B".as_bytes()), vec![1, 0]);
        assert_eq!(super::encode(&tree, "C".as_bytes()), vec![1, 1, 1]);
        assert_eq!(super::encode(&tree, "D".as_bytes()), vec![1, 1, 0]);

        assert_eq!(super::encode(&tree, "".as_bytes()), vec![]);

        assert_eq!(super::encode(&tree, "AAAABBBCCD".as_bytes()), vec![0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0]);
    }

    #[test]
    fn decode() {
        let mut tree = HuffmanTree::new();
        let dictionary = "AAAABBBCCD";
        tree.build(dictionary.as_bytes());

        assert_eq!(str::from_utf8(super::decode(&tree, &[0]).as_slice()).unwrap(), "A");
        assert_eq!(str::from_utf8(super::decode(&tree, &[1, 0]).as_slice()).unwrap(), "B");
        assert_eq!(str::from_utf8(super::decode(&tree, &[1, 1, 1]).as_slice()).unwrap(), "C");
        assert_eq!(str::from_utf8(super::decode(&tree, &[1, 1, 0]).as_slice()).unwrap(), "D");

        assert_eq!(str::from_utf8(super::decode(&tree, &[]).as_slice()).unwrap(), "");
    }

    #[test]
    fn together() {
        let mut tree = HuffmanTree::new();
        let sentence = "Today, I walked over the Brooklyn Bridge.";
        tree.build(sentence.as_bytes());

        let encoded = super::encode(&tree, sentence.as_bytes());
        assert_eq!(str::from_utf8(super::decode(&tree, encoded.as_slice()).as_slice()).unwrap(), "Today, I walked over the Brooklyn Bridge.");
    }
}
