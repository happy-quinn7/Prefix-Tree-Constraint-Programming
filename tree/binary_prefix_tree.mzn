int: n;          % number of inputs
int: radix;      % max number of children per op

string: name;

bool: commutative;

array[int] of int: arrival_list;        % arrival time of each input
array[int] of int: op_delay_list;       % delays for each of the operators (entry 1 is binary operator)
array[int] of int: op_cost_list;        % costs for each of the operators (entry 1 is binary operator)


%limits/deadlines, where -1 is no limit. required is the required time at root
int: required;
int: max_depth;
int: max_delay;
int: max_size;
int: max_cost;
int: max_ops_per_level;

set of int: LEAF = assert(n >= 2, "n must be >= 2", 0..n-1);     % assert is up here as its the first usage of n
set of int: OP = n..2*n-2;
set of int: NODE = 0..2*n-2;

int: NONE = 2*n-1;      %dummy parent of root and of unused operators

int: Tmax = assert(radix >= 2, "radix check", max(arrival_list) + (n - 1)*max(op_delay_list));  % upper bound of any arrival or finish time


% asserts for checking that the data is usable and correct, some declarations wrapped into the asserts
array[LEAF] of int: arrival =
  assert(length(arrival_list) = n, "arrival length check",
  array1d(LEAF, arrival_list));

array[int] of int: op_delay =
 assert(length(op_delay_list) = radix - 1, "op_delay length check",
 array1d(2..radix, op_delay_list));

array[int] of int: op_cost =
  assert(length(op_cost_list) = radix - 1, "op_cost length check",
  array1d(2..radix, op_cost_list));

constraint assert(forall(e in arrival_list)(e >= 0), "arrival_list elts >= 0");
constraint assert(forall(e in op_delay_list)(e >= 1), "op_delay_list elts >= 1");
constraint assert(forall(e in op_cost_list)(e >= 0), "op_cost_list elts >= 0");

constraint assert(required == -1 \/ required >= 1, "required limits");
constraint assert(max_depth == -1 \/ max_depth >= 1, "max_depth limits");
constraint assert(max_delay == -1 \/ max_delay >= 1, "max_delay limit");
constraint assert(max_size == -1 \/ max_size >= 1, "max_size limit");
constraint assert(max_cost == -1 \/ max_cost >= 1, "max_cost limit");
constraint assert(max_ops_per_level == -1 \/ max_ops_per_level >= 1, "max_ops_per_level limit");


% our two arrays that define the base behaviour of the tree, parent defining the parents of each NODE, and arity defining number of children, 0 = unused.
array[NODE] of var n..NONE: parent;
array[OP] of var 0..radix: arity;

array[NODE] of var 0..n: cnt; % where 0 means unused
array[NODE] of var 0..n-1: hi;
array[NODE] of var 0..n-1: lo;



% our basic predicates for defining the behaviour of the tree, familiar rules for the definition of a tree

% parent has a higher index than it's child
predicate parent_larger() =
  forall(v in NODE)(parent[v] > v);
  
% every input has a real parent (never root)
predicate leaf_has_parent() = 
  forall(v in LEAF)(parent[v] != NONE);
  
% arity = num. nodes whose parent is v
predicate arity_check() =
  forall(v in OP)(arity[v] != 1);
  
predicate arity_set() = 
  forall(v in OP)(count(u in NODE)((parent[u] = v)) = arity[v]);

% used operators come first, so no gap in the slots
predicate previous_has_to_be_used() = 
  forall(v in OP where v + 1 in OP)(arity[v+1] >= 2 -> arity[v] >= 2);

% unused operator has parent NONE
predicate unused_parent() =
  forall(v in OP)(arity[v] = 0 -> parent[v] = NONE);

% a used operator is the root when the next slot is unused
predicate root_is_last_used() =
  forall(v in OP where v + 1 in OP)(arity[v] >= 2 ->
   (parent[v] = NONE <-> arity[v+1] = 0));

% for unused operators, cnt,lo,hi = 0
predicate unused_cnt_lo_hi_zero() = 
  forall(v in OP)(arity[v] = 0 -> (cnt[v] = 0 /\ lo[v] = 0 /\ hi[v] = 0));

% cnt of operator = sum of it's children's count
predicate cnt_value() =
  forall(v in OP)(arity[v] >= 2 -> (sum(u in NODE)(bool2int(parent[u] = v) * cnt[u]) = cnt[v]));
  
% leaf's cnt = 1
predicate cnt_one_leaf() = 
  forall(v in LEAF)(cnt[v] = 1);

% leaf has no subtree, t.f hi = lo = v
predicate hi_lo_leaf() = 
  forall(v in LEAF)(hi[v] = v /\ lo[v] = v);

% hi of an operator is at least every child's hi
predicate hi_at_least_childs_hi() = 
  forall(v in OP)(arity[v] >= 2 -> (forall(u in NODE)(parent[u] = v -> hi[v] >= hi[u])));

% hi of an operator equals the max of the children's hi
predicate hi_equals_child() = 
  forall(v in OP)(arity[v] >= 2 -> (exists(u in NODE)(parent[u] = v /\ hi[v] = hi[u])));
  
% lo of an operator is at most every child's lo
predicate lo_at_most_childs_lo() = 
  forall(v in OP)(arity[v] >= 2 -> (forall(u in NODE)(parent[u] = v -> lo[v] <= lo[u])));

% lo of an operator is the minimum of the children's lo
predicate lo_equals_child() = 
  forall(v in OP)(arity[v] >= 2 -> (exists(u in NODE)(parent[u] = v /\ lo[v] = lo[u])));

% symmetry - used operators are ordered by non-decreasing
predicate hi_ordering() = 
  forall(v in OP where v + 1 in OP)(arity[v+1] >= 2 -> hi[v] <= hi[v+1]);
  
% commutativity predicate
predicate contiguous_when_ordered() = 
  if not(commutative) then
    forall(v in OP)(arity[v] >= 2 -> (hi[v] - lo[v] + 1 = cnt[v]))
  else true
  endif;
    
  
   
constraint parent_larger();
constraint leaf_has_parent();
constraint arity_check();
constraint arity_set();
constraint previous_has_to_be_used();
constraint unused_parent();
constraint root_is_last_used();

constraint unused_cnt_lo_hi_zero();
constraint cnt_value();
constraint cnt_one_leaf();

constraint hi_lo_leaf();
constraint hi_at_least_childs_hi();
constraint hi_equals_child();
constraint lo_at_most_childs_lo();
constraint lo_equals_child();
constraint hi_ordering();

constraint contiguous_when_ordered();

solve satisfy;


output["parent: \(parent)\narity: \(arity)\ncnt: \(cnt)\nhi: \(hi)\nlo: \(lo)\n"];

% Timing: start and ready times per node 
% Metrics: size, cost, depth, delay, width 
% Limits from the dzn 
% Objectives: one metric or a ranked combination
% Checks: known optima, evaluation pass, Python checker, test runner, edge cases 
% Move on to proper, full prefix graph