use std::collections::BinaryHeap;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Debug, Formatter, Result};

const ACTIONS: [(isize, isize); 4] = [(1, 0), (0, -1), (-1, 0), (0, 1)];

pub struct SegTree<X: Clone> {
    n: usize,
    fx: fn(X, X) -> X,
    ex: X,
    pub dat: Vec<X>,
}

impl<X: Clone> SegTree<X> {
    pub fn new(n_: usize, fx: fn(X, X) -> X, ex: X) -> Self {
        let mut x = 1;
        while n_ > x {
            x *= 2;
        }
        let n = x;
        let dat = vec![ex.clone(); n * 4];
        SegTree { n, fx, ex, dat }
    }

    pub fn set(&mut self, i: usize, v: X) {
        self.dat[i + self.n - 1] = v;
    }

    pub fn build(&mut self) {
        for k in (0..(self.n - 1)).rev() {
            self.dat[k] = (self.fx)(self.dat[2 * k + 1].clone(), self.dat[2 * k + 2].clone());
        }
    }

    pub fn update(&mut self, i: usize, v: X) {
        let mut i = i + self.n - 1;
        self.dat[i] = v;
        while i > 0 {
            i = (i - 1) / 2;
            self.dat[i] = (self.fx)(self.dat[2 * i + 1].clone(), self.dat[2 * i + 2].clone());
        }
    }

    fn query_sub(&self, a: usize, b: usize, k: usize, l: usize, r: usize) -> X {
        if r <= a || b <= l {
            self.ex.clone()
        } else if a <= l && r <= b {
            self.dat[k].clone()
        } else {
            let vl = self.query_sub(a, b, 2 * k + 1, l, (l + r) / 2);
            let vr = self.query_sub(a, b, 2 * k + 2, (l + r) / 2, r);
            (self.fx)(vl, vr)
        }
    }

    pub fn query(&self, a: usize, b: usize) -> X {
        self.query_sub(a, b, 0, 0, self.n)
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
struct Puzzle {
    n: usize,
    m: usize,
    board: Vec<Vec<usize>>,
    space_pos: (usize, usize),
    count: usize,
    heuristic: usize,
    before_action: Option<(isize, isize)>,
    parent: Option<Box<Puzzle>>,
}

impl Puzzle {
    fn new(n: usize, m: usize, board: Vec<Vec<usize>>) -> Self {
        let mut space_pos = (0, 0);
        for i in 0..n {
            for j in 0..m {
                if board[i][j] == 0 {
                    space_pos = (j, i);
                }
            }
        }
        Self {
            n,
            m,
            board,
            space_pos,
            count: 0,
            heuristic: 0,
            before_action: None,
            parent: None,
        }
    }

    fn step(&mut self, action: (isize, isize)) -> bool {
        let (x, y) = self.space_pos;
        let (dx, dy) = action;
        let (nx, ny) = (x as isize + dx, y as isize + dy);
        if nx < 0 || nx >= self.n as isize || ny < 0 || ny >= self.m as isize {
            return false;
        }
        let (nx, ny) = (nx as usize, ny as usize);
        self.board[y][x] = self.board[ny][nx];
        self.board[ny][nx] = 0;
        self.space_pos = (nx, ny);
        self.count += 1;
        self.heuristic = get_manhattan_distance(self);
        self.before_action = Some(action);
        true
    }

    fn get_state(&self) -> Vec<Vec<usize>> {
        self.board.clone()
    }

    fn get_legal_actions(&self) -> Vec<(isize, isize)> {
        let mut actions = Vec::new();
        for action in ACTIONS.iter() {
            let (x, y) = self.space_pos;
            let (dx, dy) = *action;
            let (nx, ny) = (x as isize + dx, y as isize + dy);
            if nx < 0 || nx >= self.n as isize || ny < 0 || ny >= self.m as isize {
                continue;
            }
            actions.push(*action);
        }
        actions
    }
}

impl Debug for Puzzle {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        for i in 0..self.n {
            for j in 0..self.m {
                if j < self.m - 1 {
                    write!(f, "{} ", self.board[i][j])?;
                } else {
                    write!(f, "{}", self.board[i][j])?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl PartialOrd for Puzzle {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(
            (self.count + self.heuristic)
                .cmp(&(other.count + other.heuristic))
                .reverse(),
        )
    }
}

impl Ord for Puzzle {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.count + self.heuristic)
            .cmp(&(other.count + other.heuristic))
            .reverse()
    }
}

fn get_reverse_action(action: (isize, isize)) -> (isize, isize) {
    let (dx, dy) = action;
    (-dx, -dy)
}

fn is_valid(puzzle: &Puzzle) -> bool {
    let (n, m) = (puzzle.n, puzzle.m);
    let mut a = vec![false; n * m];
    let mut zero_found = false;
    for i in 0..n {
        for j in 0..m {
            let v = puzzle.board[i][j];
            if v == 0 {
                if zero_found {
                    return false;
                }
                zero_found = true;
                continue;
            }
            if v > n * m {
                return false;
            }
            if a[v - 1] {
                return false;
            }
            a[v - 1] = true;
        }
    }
    true
}

fn is_solvable(puzzle: &Puzzle) -> bool {
    let mut inv = 0;
    let n_ = puzzle.n * puzzle.m;
    let mut a = Vec::new();
    for i in 0..puzzle.n {
        for j in 0..puzzle.m {
            a.push(puzzle.board[i][j]);
        }
    }
    let (sx, sy) = puzzle.space_pos;
    let s_index = sy * puzzle.m + sx;
    a[s_index] = n_;
    let mut seg_tree = SegTree::new(n_, |x, y| x + y, 0);
    for i in 0..n_ {
        let v = a[i] - 1;
        inv += v - seg_tree.query(0, v);
        seg_tree.update(v, 1);
    }
    (inv % 2 == 0) == (((puzzle.n - 1 - sy) + (puzzle.m - 1 - sx)) % 2 == 0)
}

fn create_goal(puzzle: &Puzzle) -> Vec<Vec<usize>> {
    let (n, m) = (puzzle.n, puzzle.m);
    let mut goal = vec![];
    for i in 0..n {
        let mut line = vec![];
        for j in 0..m {
            line.push(i * m + j + 1);
        }
        goal.push(line);
    }
    goal[n - 1][m - 1] = 0;
    goal
}

fn bfs(puzzle: &Puzzle) -> Option<Vec<(isize, isize)>> {
    let mut queue = VecDeque::new();
    let mut visited = HashSet::new();
    let mut parent = HashMap::new();
    queue.push_back(puzzle.get_state());
    visited.insert(puzzle.get_state());
    let goal = create_goal(puzzle);
    let mut visited_count = 0;
    while let Some(state) = queue.pop_front() {
        visited_count += 1;
        eprint!("\r{}", visited_count);
        let mut puzzle = Puzzle::new(puzzle.n, puzzle.m, state);
        if puzzle.get_state() == goal {
            let mut path = Vec::new();
            let mut state = puzzle.get_state();
            while let Some(action) = parent.get(&state) {
                let reverse_action = get_reverse_action(*action);
                path.push(*action);
                puzzle.step(reverse_action);
                state = puzzle.get_state();
            }
            path.reverse();
            // println!("visited count: {}", visited_count);
            return Some(path);
        }
        for action in puzzle.get_legal_actions() {
            let mut puzzle = puzzle.clone();
            puzzle.step(action);
            let state = puzzle.get_state();
            if visited.contains(&state) {
                continue;
            }
            queue.push_back(state.clone());
            visited.insert(state.clone());
            parent.insert(state, action);
        }
    }
    None
}

fn get_manhattan_distance(puzzle: &Puzzle) -> usize {
    let mut distance = 0;
    for i in 0..puzzle.n {
        for j in 0..puzzle.m {
            let v = puzzle.board[i][j];
            if v == 0 {
                continue;
            }
            let (x, y) = ((v - 1) % puzzle.m, (v - 1) / puzzle.m);
            distance +=
                (x as isize - j as isize).abs() as usize + (y as isize - i as isize).abs() as usize;
        }
    }
    distance
}

fn a_star(puzzle: &Puzzle) -> Option<Vec<(isize, isize)>> {
    let mut puzzle = puzzle.clone();
    let mut queue = BinaryHeap::new();
    let mut visited = HashMap::new();
    // let mut before_action = HashMap::new();
    let goal = create_goal(&puzzle);
    puzzle.heuristic = get_manhattan_distance(&puzzle);
    queue.push(puzzle.clone());
    let mut visited_count = 0;
    while let Some(mut puzzle) = queue.pop() {
        visited_count += 1;
        eprint!("\r{}", visited_count);
        if puzzle.get_state() == goal {
            let mut path = Vec::new();
            while let Some(parent) = puzzle.parent {
                let action = puzzle.before_action.unwrap();
                path.push(action);
                puzzle = *parent;
            }
            path.reverse();
            // println!("visited count: {}", visited_count);
            return Some(path);
        }
        visited.insert(puzzle.board.clone(), puzzle.clone());
        for action in puzzle.get_legal_actions() {
            let mut next_puzzle = puzzle.clone();
            next_puzzle.step(action);
            next_puzzle.parent = Some(Box::new(puzzle.clone()));
            let state = next_puzzle.get_state();
            if let Some(puzzle) = visited.get(&state) {
                if *puzzle <= next_puzzle {
                    continue;
                }
            }
            queue.push(next_puzzle.clone());
        }
    }
    None
}

fn get_inversion_number_without_segtree(a: Vec<usize>) -> usize {
    let n = a.len();
    let mut inv = 0;
    for i in 0..n {
        for j in 0..i {
            if a[j] > a[i] {
                inv += 1;
            }
        }
    }
    inv
}

fn main() {
    let board = vec![
        vec![2, 1, 3, 4],
        vec![5, 6, 7, 8],
        vec![9, 10, 11, 12],
        vec![13, 15, 14, 0],
    ];
    let mut puzzle = Puzzle::new(4, 4, board);
    println!("{:?}", puzzle);
    if !is_valid(&puzzle) {
        println!("invalid");
        return;
    }
    if !is_solvable(&puzzle) {
        println!("unsolvable");
        return;
    }
    // if let Some(path) = bfs(&puzzle) {
    //     for action in path {
    //         println!("{:?}", action);
    //         puzzle.step(action);
    //         println!("{:?}", puzzle);
    //     }
    // }
    if let Some(path) = a_star(&puzzle) {
        for action in path {
            println!("{} {}", action.0, action.1);
            puzzle.step(action);
            // println!("{:?}", puzzle);
        }
    }
}
