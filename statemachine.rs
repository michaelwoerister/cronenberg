// Copyright (c) 2014 Michael Woerister

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

use std::rc::Rc;
use std::hashmap::{HashMap, HashSet};
use std::sync::atomics::{AtomicUint, INIT_ATOMIC_UINT, SeqCst};

#[deriving(IterBytes, Clone, Eq, TotalEq)]
pub struct StateId {
    machine_id: uint,
    local_id: uint
}

#[deriving(IterBytes, Clone, Eq)]
pub enum TransitionCondition {
    Char(char),
    Epsilon
}

impl TransitionCondition {
    fn intersects(&self, other: &TransitionCondition) -> bool {
        match (*self, *other) {
            (Char(c1), Char(c2)) => (c1 == c2),
            (Epsilon, Epsilon) => true,
            _ => false
        }
    }
}

#[deriving(Clone)]
pub struct State {
	priv transitions: HashMap<TransitionCondition, ~[StateId]>
}

#[deriving(Clone)]
pub struct StateMachine {
    priv states: HashMap<StateId, State>,
    priv state_id_counter: uint,
    priv machine_id: uint,
}

pub type StateSet = HashSet<StateId>;

pub struct ToDfaResult {
    dfa: StateMachine,
    start_state: StateId,
    end_state_map: HashMap<StateId, ~[StateId]>,
}

fn any_from<T: IterBytes + Eq + Pod>(state_set: &HashSet<T>) -> T {
    assert!(state_set.len() > 0);
    *state_set.iter().next().unwrap()
}

impl IterBytes for StateSet {

    // inefficient due to allocation and sorting
    fn iter_bytes(&self, lsb0: bool, f: ::std::to_bytes::Cb) -> bool {
        let mut sorted: ~[StateId] = self.iter().map(|x| *x).collect();
        sorted.sort_by(|a, b| {
            let m_id = a.machine_id.cmp(&b.machine_id);
            if m_id != Equal {
                m_id
            } else {
                a.local_id.cmp(&b.local_id)
            }
        });

        return sorted.iter_bytes(lsb0, |x| f(x));
    }
}

impl ::std::cmp::Equiv<Rc<StateSet>> for StateSet {
    fn equiv(&self, other: &Rc<StateSet>) -> bool {
        *self == *other.borrow()
    }
}

impl ::std::cmp::TotalOrd for TransitionCondition {
    fn cmp(&self, other: &TransitionCondition) -> Ordering {
        let self_int = match *self {
            Epsilon => -1,
            Char(c) => c as i64
        };

        let other_int = match *other {
            Epsilon => -1,
            Char(c) => c as i64
        };

        return self_int.cmp(&other_int);
    }
}

impl ::std::cmp::TotalEq for TransitionCondition {
    fn equals(&self, other: &TransitionCondition) -> bool {
        return *self == *other;
    }
}

impl StateMachine {

    pub fn new() -> StateMachine {
        static mut id_counter: AtomicUint = INIT_ATOMIC_UINT;

        StateMachine {
            states: HashMap::new(),
            state_id_counter: 0,
            machine_id: unsafe { id_counter.fetch_add(1, SeqCst) },
        }
    }

	pub fn is_deterministic(&self) -> bool {
		for state in self.states.values() {
            if state.transitions.contains_key(&Epsilon) {
                return false;
            }

			if state.transitions.values().any(|dests| dests.len() > 1) {
				return false;
			}

            let conditions = state.transitions.keys().to_owned_vec();

            for i1 in range(0, conditions.len()) {
                for i2 in range(0, conditions.len()) {
                    if i1 != i2 && conditions[i1].intersects(conditions[i2]) {
                        return false;
                    }
                }
            }
		}

		return true;
	}

    pub fn add_state(&mut self) -> StateId {
        let local_id = self.state_id_counter;
        self.state_id_counter += 1;

        let state_id = StateId { local_id: local_id, machine_id: self.machine_id };
        self.states.insert(state_id, State { transitions: HashMap::new() });

        return state_id;
    }

    pub fn add_transition(&mut self, from: StateId, to: StateId, condition: TransitionCondition) {
        assert!(self.contains_state(from));
        assert!(self.contains_state(to));

        self.states
            .get_mut(&from)
            .transitions
            .find_or_insert_with(condition, |_| ~[])
            .push(to);
    }

    pub fn contains_state(&self, state: StateId) -> bool {
        self.states.contains_key(&state)
    }

    pub fn contains_transition(&self,
                               from: StateId,
                               to: StateId,
                               condition: TransitionCondition)
                            -> bool {
        match self.states.find(&from) {
            Some(state) => {
                match state.transitions.find(&condition) {
                    Some(dests) => dests.iter().any(|dest| *dest == to),
                    _ => false
                }
            },
            _ => false
        }
    }

    pub fn consume(&mut self, lunch: StateMachine) {
        for (k, v) in lunch.states.move_iter() {
            assert!(!self.states.contains_key(&k));
            self.states.insert(k, v);
        }
    }

    fn epsilon_closure(&self, state: StateId) -> StateSet {
        assert!(self.states.contains_key(&state));

        let mut output = HashSet::new();
        collect(self, state, &mut output);
        return output;

        fn collect(sm: &StateMachine,
                   current: StateId,
                   output: &mut StateSet) {
            if output.iter().any(|&x| x == current) {
                return;
            }

            output.insert(current);

            let transitions = &sm.states.get(&current).transitions;

            transitions.find(&Epsilon).map(
                |transitions| {
                    for &state in transitions.iter() {
                        collect(sm, state, output);
                    }
                });
        }
    }

    fn move(&self, state_set: &StateSet, condition: TransitionCondition) -> StateSet {
        let mut output = HashSet::new();

        for state in state_set.iter() {
            let transitions = &self.states.get(state).transitions;

            match transitions.find(&condition) {
                Some(dests) => {
                    let mut state_ids = dests.iter().map(|&x| x);
                    output.extend(&mut state_ids);
                },
                None => {}
            };
        }

        return output;
    }

    fn epsilon_closure_set(&self, state_set: &StateSet) -> StateSet {
        let mut output = HashSet::new();

        for &state in state_set.iter() {
            let closure = self.epsilon_closure(state);
            output.extend(&mut closure.iter().map(|&x| x));
        }

        return output;
    }

    fn has_dangling_transitions(&self) -> bool {
        for dest_state in self.states
                              .values()
                              .flat_map(|s| s.transitions.values())
                              .flat_map(|x| x.iter()) {
            if !self.states.contains_key(dest_state) {
                return true;
            }
        }

        return false;
    }

    pub fn to_dfa(&self, nfa_start_state: StateId, nfa_end_states: &StateSet) -> ToDfaResult {
        assert!(self.states.contains_key(&nfa_start_state));
        assert!(!self.has_dangling_transitions());
        assert!(!self.is_deterministic());

        let mut dfa = StateMachine::new();
        let mut nfa_to_dfa: HashMap<Rc<StateSet>, StateId> = HashMap::new();
        let mut dfa_to_nfa: HashMap<StateId, Rc<StateSet>> = HashMap::new();
        let mut marked_dfa: StateSet = HashSet::new();

        let dfa_start_state = dfa.add_state();
        let nfa_start_state_closure = Rc::new(self.epsilon_closure(nfa_start_state));
        nfa_to_dfa.insert(nfa_start_state_closure.clone(), dfa_start_state);
        dfa_to_nfa.insert(dfa_start_state, nfa_start_state_closure);

        while dfa.states.len() > marked_dfa.len() {
            let current = *dfa.states.keys().find(|&id| !marked_dfa.contains(id)).unwrap();
            marked_dfa.insert(current);

            let source_nfa_state_set = dfa_to_nfa.get_copy(&current);

            let mut symbols = ~[];
            for nfa_state in source_nfa_state_set.borrow().iter() {
                for &symbol in self.states.get(nfa_state).transitions.keys() {
                    if symbol != Epsilon {
                        symbols.push(symbol);
                    }
                }
            }

            for &symbol in symbols.iter() {
                assert!(symbol != Epsilon);

                let dest_nfa_state_set = self.epsilon_closure_set(
                    &self.move(source_nfa_state_set.borrow(), symbol));

                let other_state = match nfa_to_dfa.find_equiv(&dest_nfa_state_set) {
                    None => {
                        let dest_nfa_state_set = Rc::new(dest_nfa_state_set);
                        let new_state = dfa.add_state();

                        nfa_to_dfa.insert(dest_nfa_state_set.clone(), new_state);
                        dfa_to_nfa.insert(new_state, dest_nfa_state_set);
                        new_state
                    }
                    Some(&state) => state
                };

                dfa.add_transition(current, other_state, symbol);
            }
        }

        assert!(!dfa.has_dangling_transitions());
        assert!(dfa.is_deterministic());

        let mut end_state_map = HashMap::new();

        for nfa_end_state in nfa_end_states.iter() {
            let mut mapping = ~[];

            for (nfa_state_set, &dfa_state) in nfa_to_dfa.iter() {
                if nfa_state_set.borrow().contains(nfa_end_state) {
                    mapping.push(dfa_state);
                }
            }

            end_state_map.insert(*nfa_end_state, mapping);
        }

        return ToDfaResult{
            dfa: dfa,
            start_state: dfa_start_state,
            end_state_map: end_state_map,
        };
    }

    pub fn run(&self, start_state: StateId, input: &str) -> Option<StateId> {
        assert!(self.is_deterministic());
        assert!(self.states.contains_key(&start_state));
        assert!(!self.has_dangling_transitions());

        let mut current_state = start_state;

        for input_char in input.chars().map(|c| Char(c)) {
            match self.states.get(&current_state).transitions.find(&input_char) {
                Some(dests) => {
                    assert!(dests.len() == 1);
                    current_state = dests[0];
                }
                None => return None
            };
        }

        return Some(current_state);
    }

    pub fn accepting_non_accepting_partitioning<T: Iterator<StateId>>(&self,
                                                                      mut accepting_states: T)
                                                                   -> Partitioning {
        let accepting_states = accepting_states.collect::<StateSet>();

        let non_accepting = self.states
                                .keys()
                                .filter(|&s| !accepting_states.contains(s))
                                .map(|x| *x)
                                .collect::<StateSet>();

        Partitioning(~[accepting_states, non_accepting])
    }

    pub fn to_minimal(&self, initial_partitioning: &Partitioning)
               -> (StateMachine, HashMap<StateId, StateId>) {
        assert!(!self.has_dangling_transitions());
        assert!(self.is_deterministic());

        let mut p = self.partition_by_transition_condition_set(initial_partitioning);

        loop {
            let new_partitioning = self.partition_further(&p);

            if new_partitioning == p {
                return self.from_partitioning(&new_partitioning);
            } else {
                p = new_partitioning;
            }
        }
    }

    fn from_partitioning(&self, &Partitioning(ref state_sets): &Partitioning)
                      -> (StateMachine, HashMap<StateId, StateId>) {
        let mut new_state_machine = StateMachine::new();
        let mut old_state_to_new_state = HashMap::new();
        let mut reps = ~[];

        for state_set in state_sets.iter() {
            let new_state = new_state_machine.add_state();

            reps.push(any_from(state_set));

            for &old_state in state_set.iter() {
                old_state_to_new_state.insert(old_state, new_state);
            }
        }

        for rep in reps.iter() {
            let transitions = &self.states.get(rep).transitions;
            let new_state = old_state_to_new_state.get_copy(rep);

            for (&symbol, dest_states) in transitions.iter() {
                assert!(dest_states.len() == 1);
                let new_dest_state = old_state_to_new_state.get_copy(dest_states.head());
                new_state_machine.add_transition(new_state, new_dest_state, symbol);
            }
        }

        assert!(!new_state_machine.has_dangling_transitions());
        assert!(new_state_machine.is_deterministic());
        (new_state_machine, old_state_to_new_state)
    }

    fn partition_further(&self, &Partitioning(ref old_state_sets): &Partitioning) -> Partitioning {
        type GroupId = uint;

        let mut new_state_sets = ~[];

        for state_set in old_state_sets.iter() {
            assert!(state_set.len() > 0);
            assert!(self.have_same_transition_conditions(state_set));

            // Find all transition symbols for this group
            let symbols = self.states
                              .get(&any_from(state_set))
                              .transitions
                              .keys()
                              .to_owned_vec();

            // Build a map that sub-divides this group into smaller groups
            let mut grouped_by_transitions = HashMap::<~[(TransitionCondition, GroupId)],
                                                       ~[StateId]>::new();

            for state in state_set.iter() {
                // Build the key for this state. States that transition into the same destination
                // group on the same input symbol (for all symbols) will receive the same key.
                let key = symbols.iter().map(|&symbol| {
                    assert!(self.states.get(state).transitions.get(symbol).len() == 1);
                    let dest_state = self.states.get(state).transitions.get(symbol).head();
                    let dest_group = find_group_of_state(dest_state, old_state_sets);
                    (*symbol, dest_group)
                }).collect();

                // Add the state to the list for the computed key
                let group = grouped_by_transitions.find_or_insert_with(key, |_| ~[]);
                group.push(*state);
            }

            for sub_state_set in grouped_by_transitions.values() {
                new_state_sets.push(sub_state_set.iter().map(|x| *x).collect());
            }
        }

        let new_partitioning = Partitioning(new_state_sets);
        assert!(self.is_valid_partitioning(&new_partitioning));
        return new_partitioning;


        fn find_group_of_state(state_id: &StateId, state_sets: &~[StateSet]) -> GroupId {
            let index = state_sets.iter().position(|state_set| state_set.contains(state_id));
            assert!(index.is_some());
            return index.unwrap();
        }
    }

    fn partition_by_transition_condition_set(&self,
                                             &Partitioning(ref state_sets): &Partitioning)
                                          -> Partitioning {
        let mut new_state_sets = ~[];

        for state_set in state_sets.iter() {
            let mut grouped_by_transition_symbols = HashMap::<~[TransitionCondition],
                                                              ~[StateId]>::new();

            for state_id in state_set.iter() {
                let mut key: ~[TransitionCondition] = self.states
                                                      .get(state_id)
                                                      .transitions
                                                      .keys()
                                                      .map(|x| *x)
                                                      .collect();
                key.sort_by(|a, b| a.cmp(b));

                grouped_by_transition_symbols
                    .find_or_insert_with(key, |_| ~[])
                    .push(*state_id);
            }

            for state_set in grouped_by_transition_symbols.values() {
                new_state_sets.push(state_set.iter().map(|x| *x).collect());
            }
        }

        let new_partitioning = Partitioning(new_state_sets);
        assert!(self.is_valid_partitioning(&new_partitioning));
        return new_partitioning;
    }

    fn is_valid_partitioning(&self, &Partitioning(ref state_sets): &Partitioning) -> bool {
        let states: StateSet = state_sets.iter()
                                         .flat_map(|state_set| state_set.iter())
                                         .map(|x| *x)
                                         .collect();

        return states == self.states.keys().map(|x| *x).collect();
    }

    fn have_same_transition_conditions(&self, state_set: &StateSet) -> bool {
        assert!(state_set.len() > 0);
        let expected_symbols = self.states
                                   .get(&any_from(state_set))
                                   .transitions
                                   .keys()
                                   .map(|x| *x)
                                   .collect::<HashSet<TransitionCondition>>();

        for state_id in state_set.iter() {
            let transitions_symbols = self.states
                                          .get(state_id)
                                          .transitions
                                          .keys()
                                          .map(|x| *x)
                                          .collect::<HashSet<TransitionCondition>>();
            if expected_symbols != transitions_symbols {
                return false;
            }
        }

        return true;
    }
}

#[deriving(Eq)]
struct Partitioning(~[StateSet]);

#[cfg(test)]
mod test {
    use super::{StateId, StateMachine, Epsilon, Char, StateSet};

    #[test]
    fn test_add_state() {
        let mut sm = StateMachine::new();

        let state1 = sm.add_state();
        assert!(sm.contains_state(state1));

        let state2 = sm.add_state();
        assert!(sm.contains_state(state1));
        assert!(sm.contains_state(state2));

        let state3 = sm.add_state();
        assert!(sm.contains_state(state1));
        assert!(sm.contains_state(state2));
        assert!(sm.contains_state(state3));
    }


    #[test]
    fn test_add_transition_dfa() {
        let mut sm = StateMachine::new();

        let state1 = sm.add_state();
        let state2 = sm.add_state();

        assert!(!sm.contains_transition(state1, state2, Char('a')));
        assert!(!sm.contains_transition(state1, state2, Char('b')));
        assert!(!sm.contains_transition(state1, state2, Char('c')));

        assert!(!sm.contains_transition(state2, state1, Char('a')));
        assert!(!sm.contains_transition(state2, state1, Char('b')));
        assert!(!sm.contains_transition(state2, state1, Char('c')));

        assert!(sm.is_deterministic());

        sm.add_transition(state1, state2, Char('a'));
        assert!(sm.contains_transition(state1, state2, Char('a')));
        assert!(!sm.contains_transition(state1, state2, Char('b')));
        assert!(!sm.contains_transition(state1, state2, Char('c')));

        assert!(!sm.contains_transition(state2, state1, Char('a')));
        assert!(!sm.contains_transition(state2, state1, Char('b')));
        assert!(!sm.contains_transition(state2, state1, Char('c')));

        assert!(sm.is_deterministic());

        sm.add_transition(state1, state2, Char('b'));
        assert!(sm.contains_transition(state1, state2, Char('a')));
        assert!(sm.contains_transition(state1, state2, Char('b')));
        assert!(!sm.contains_transition(state1, state2, Char('c')));

        assert!(!sm.contains_transition(state2, state1, Char('a')));
        assert!(!sm.contains_transition(state2, state1, Char('b')));
        assert!(!sm.contains_transition(state2, state1, Char('c')));

        assert!(sm.is_deterministic());

        sm.add_transition(state1, state2, Char('c'));
        assert!(sm.contains_transition(state1, state2, Char('a')));
        assert!(sm.contains_transition(state1, state2, Char('b')));
        assert!(sm.contains_transition(state1, state2, Char('c')));

        assert!(!sm.contains_transition(state2, state1, Char('a')));
        assert!(!sm.contains_transition(state2, state1, Char('b')));
        assert!(!sm.contains_transition(state2, state1, Char('c')));

        assert!(sm.is_deterministic());
    }

    #[test]
    fn test_add_transition_nfa() {
        let mut sm = StateMachine::new();

        let state1 = sm.add_state();
        let state2 = sm.add_state();
        let state3 = sm.add_state();

        assert!(!sm.contains_transition(state1, state2, Char('a')));
        assert!(!sm.contains_transition(state1, state3, Char('a')));
        assert!(sm.is_deterministic());

        sm.add_transition(state1, state2, Char('a'));
        assert!(sm.contains_transition(state1, state2, Char('a')));
        assert!(!sm.contains_transition(state1, state3, Char('a')));
        assert!(sm.is_deterministic());

        sm.add_transition(state1, state3, Char('a'));
        assert!(sm.contains_transition(state1, state2, Char('a')));
        assert!(sm.contains_transition(state1, state3, Char('a')));
        assert!(!sm.is_deterministic());
    }

    #[test]
    fn test_epsilon_closure() {
    /*

    A --e--> B --e--> C --x--> D --e--> E
             |
             e
             |
             F --e--> G --x --> H <--e--> I --e--> J

    */
        let mut sm = StateMachine::new();

        let A = sm.add_state();
        let B = sm.add_state();
        let C = sm.add_state();
        let D = sm.add_state();
        let E = sm.add_state();
        let F = sm.add_state();
        let G = sm.add_state();
        let H = sm.add_state();
        let I = sm.add_state();
        let J = sm.add_state();

        sm.add_transition(A, B, Epsilon);
        sm.add_transition(B, C, Epsilon);
        sm.add_transition(C, D, Char('x'));
        sm.add_transition(D, E, Epsilon);
        sm.add_transition(B, F, Epsilon);
        sm.add_transition(F, G, Epsilon);
        sm.add_transition(G, H, Char('x'));
        sm.add_transition(H, I, Epsilon);
        sm.add_transition(I, H, Epsilon);
        sm.add_transition(I, J, Epsilon);

        contains_only(sm.epsilon_closure(A), [A, B, C, F, G]);
        contains_only(sm.epsilon_closure(B), [B, C, F, G]);
        contains_only(sm.epsilon_closure(C), [C]);
        contains_only(sm.epsilon_closure(D), [D, E]);
        contains_only(sm.epsilon_closure(E), [E]);
        contains_only(sm.epsilon_closure(F), [F, G]);
        contains_only(sm.epsilon_closure(G), [G]);
        contains_only(sm.epsilon_closure(H), [H, I, J]);
        contains_only(sm.epsilon_closure(I), [H, I, J]);
        contains_only(sm.epsilon_closure(J), [J]);

        fn contains_only(set: StateSet, elems: &[StateId]) {
            for e in elems.iter() {
                assert!(set.contains(e));
            }

            assert!(elems.len() == set.len());
        }
    }
}