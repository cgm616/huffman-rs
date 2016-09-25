use std::collections::BTreeMap;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

#[derive(Clone, Eq, PartialEq)]
struct FreqNode {
    freq: usize,
    node: usize,
}

#[derive(Debug)]
pub struct HuffmanTree<T> {
    dict: ElemDict<T>,
    nodes: Vec<Type<T>>,
    head: NodeRef,
}

type ElemDict<T> = BTreeMap<T, usize>;

type NodeRef = Option<usize>;

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
enum Type<T> {
    Branch(BranchNode),
    Leaf(LeafNode<T>),
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
enum Side {
    Left,
    Right,
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
struct LeafNode<T> {
    elem: T,
    side: Option<Side>,
    parent: NodeRef,
}

#[derive(Clone, Copy, Eq, PartialEq, Debug)]
struct BranchNode {
    side: Option<Side>,
    parent: NodeRef,
    left: NodeRef,
    right: NodeRef,
}

impl Ord for FreqNode {
    fn cmp(&self, other: &FreqNode) -> Ordering {
        other.freq.cmp(&self.freq)
    }
}

impl PartialOrd for FreqNode {
    fn partial_cmp(&self, other: &FreqNode) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> HuffmanTree<T> where T: std::cmp::Ord, T: std::clone::Clone, T: std::marker::Copy {
    fn new() -> Self {
        HuffmanTree { dict: BTreeMap::new(), nodes: Vec::new(), head: None }
    }

    fn build(&mut self, chars: &[T]) {
        let mut freq_counter: BTreeMap<T, usize> = BTreeMap::new();

        for elem in chars {
            *freq_counter.entry(*elem).or_insert(0) += 1;
        }

        let mut queue: BinaryHeap<FreqNode> = BinaryHeap::new();

        for (elem, freq) in freq_counter {
            let leaf = Type::Leaf(LeafNode { elem: elem, side: None, parent: None });
            self.nodes.push(leaf);
            let new_index = self.nodes.len() - 1;
            self.dict.insert(elem, new_index);
            queue.push(FreqNode { freq: freq, node: new_index });
        }

        fn update_node<U>(node: Type<U>, parent: usize, side: Side) -> Type<U> {
            match node {
                Type::Branch(node) => {
                    Type::Branch(BranchNode { side: Some(side),
                                              parent: Some(parent),
                                              left: node.left,
                                              right: node.right })
                },
                Type::Leaf(node) => {
                    Type::Leaf(LeafNode { elem: node.elem,
                                          side: Some(side),
                                          parent: Some(parent) })
                },
            }
        }

        while let Some(left_node) = queue.pop() {
            if let Some(right_node) = queue.pop() {
                let freq = left_node.freq + right_node.freq;

                let left_node = left_node.node;
                let right_node = right_node.node;

                self.nodes.push(Type::Branch(BranchNode { side: None,
                                                          parent: None,
                                                          left: Some(left_node),
                                                          right: Some(right_node) }));

                let new_index = self.nodes.len() - 1;

                self.nodes[left_node] = update_node(self.nodes[left_node], new_index, Side::Left);
                self.nodes[right_node] = update_node(self.nodes[right_node], new_index, Side::Right);

                queue.push(FreqNode { freq: freq, node: new_index });
            } else {
                self.head = Some(left_node.node);
            }
        }
    }

    fn encode(&self, chars: &[T]) -> Vec<u8> {
        let mut output: Vec<u8> = Vec::new();

        for elem in chars {
            let mut buffer: Vec<u8> = Vec::new();

            match self.dict.get(elem) {
                Some(leaf) => {
                    let mut current: Option<usize> = Some(*leaf);
                    if current == self.head {
                        buffer.push(0);
                    }
                    while let Some(index) = current {
                        match self.nodes[index] {
                            Type::Leaf(node) => {
                                match node.side {
                                    Some(Side::Left) => buffer.push(0),
                                    Some(Side::Right) => buffer.push(1),
                                    None => { /* eventually return error */ },
                                };
                                current = node.parent;
                            }
                            Type::Branch(node) => {
                                match node.side {
                                    Some(Side::Left) => buffer.push(0),
                                    Some(Side::Right) => buffer.push(1),
                                    None => { /* eventually return error */ },
                                };
                                current = node.parent;
                            }
                        }
                    }
                },
                None => { /* eventually return error */ },
            }

            buffer.reverse();
            output.append(&mut buffer);
        }

        output
    }

    fn decode(&self, bits: &[u8]) -> Vec<T> where T: std::marker::Copy {
        let mut output: Vec<T> = Vec::new();

        let mut current: Option<usize> = self.head;
        for bit in bits {
            if let Some(index) = current {
                match self.nodes[index] {
                    Type::Leaf(node) => {
                        output.push(node.elem);
                        current = self.head;
                    },
                    Type::Branch(node) => {
                        match *bit {
                            0 => {
                                if let Type::Leaf(node) = self.nodes[node.left.unwrap()] {
                                    output.push(node.elem);
                                    current = self.head;
                                } else {
                                    current = node.left;
                                }
                            },
                            1 => {
                                if let Type::Leaf(node) = self.nodes[node.right.unwrap()] {
                                    output.push(node.elem);
                                    current = self.head;
                                } else {
                                    current = node.right;
                                }
                            },
                            _ => { /* eventually return error */ }
                        }
                    },
                }
            }
        }

        output
    }
}

#[cfg(test)]
mod test {
    use std::str;
    use std::collections::BTreeMap;
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
    fn empty_tree() {
        let mut tree = HuffmanTree::new();
        tree.build("".as_bytes());

        assert_eq!(tree.dict, BTreeMap::new());
        assert_eq!(tree.nodes, Vec::new());
        assert_eq!(tree.head, None);

        /* test errors from tree.encode() and tree.decode() */
    }

    #[test]
    fn encode() {
        let mut tree = HuffmanTree::new();
        let dictionary = "AAAABBBCCD";
        tree.build(dictionary.as_bytes());

        assert_eq!(tree.encode("A".as_bytes()), [0]);
        assert_eq!(tree.encode("B".as_bytes()), [1, 0]);
        assert_eq!(tree.encode("C".as_bytes()), [1, 1, 1]);
        assert_eq!(tree.encode("D".as_bytes()), [1, 1, 0]);

        assert_eq!(tree.encode("".as_bytes()), []);

        assert_eq!(tree.encode("AAAABBBCCD".as_bytes()), [0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0]);
    }

    #[test]
    fn small_tree() {
        let mut tree = HuffmanTree::new();
        tree.build("A".as_bytes());

        assert!(tree.dict.contains_key("A".as_bytes().first().unwrap()));

        assert_eq!(tree.encode("A".as_bytes()), [0]);
        assert_eq!(tree.encode("AA".as_bytes()), [0, 0]);

        assert_eq!(tree.encode("B".as_bytes()), []);
        assert_eq!(tree.encode("BB".as_bytes()), []);

        assert_eq!(str::from_utf8(tree.decode(&[0]).as_slice()).unwrap(), "A");
        assert_eq!(str::from_utf8(tree.decode(&[1]).as_slice()).unwrap(), "A");
        assert_eq!(str::from_utf8(tree.decode(&[0, 1]).as_slice()).unwrap(), "AA");
    }

    #[test]
    fn decode() {
        let mut tree = HuffmanTree::new();
        let dictionary = "AAAABBBCCD";
        tree.build(dictionary.as_bytes());

        assert_eq!(str::from_utf8(tree.decode(&[0]).as_slice()).unwrap(), "A");
        assert_eq!(str::from_utf8(tree.decode(&[1, 0]).as_slice()).unwrap(), "B");
        assert_eq!(str::from_utf8(tree.decode(&[1, 1, 1]).as_slice()).unwrap(), "C");
        assert_eq!(str::from_utf8(tree.decode(&[1, 1, 0]).as_slice()).unwrap(), "D");

        assert_eq!(str::from_utf8(tree.decode(&[]).as_slice()).unwrap(), "");
    }

    #[test]
    fn together() {
        let mut tree = HuffmanTree::new();
        let sentence = "Today, I walked over the Brooklyn Bridge.";
        tree.build(sentence.as_bytes());

        let encoded = tree.encode(sentence.as_bytes());
        assert_eq!(str::from_utf8(tree.decode(encoded.as_slice()).as_slice()).unwrap(), "Today, I walked over the Brooklyn Bridge.");
    }
}
