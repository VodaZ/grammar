console.clear();

/////////////////////////////////////////////////
///////////////////// UTILS /////////////////////
/////////////////////////////////////////////////

const eps = 'ε';

const myUntil = (cond, f, data) => {
  let state = data;
   
  while(cond(state)) {
    state = f(state);
  };
    
  return state;
};

const sorter = (a, b) => {
    if(a < b) { return -1; }
    if(a > b) { return 1; }
    return 0;
}

const isSimpleRule = rule => {
  const [X1, X2] = rule;
  
  return rule.length === 2 && isUppercase(X1) && isUppercase(X2);
};
const filterSimpleRules = filter(isSimpleRule);
const rejectSimpleRules = reject(isSimpleRule);

const isTerminatingRule = rule => {
  const t = tail(rule);
  
  return all(isLowercase, t);
};

const filterTerminatingRules = filter(isTerminatingRule);
const rejectTerminatingRules = reject(isTerminatingRule);

const isEpsRule = rule => {
  return rule.length === 1 || (rule.length === 2 && rule[1] === eps);
};
const filterEpsRules = filter(isEpsRule);
const rejectEpsRules = reject(isEpsRule);

const removeEpsFromRule = reject(equals(eps));

const f = (a, b) => [].concat(...a.map(d => b.map(e => [].concat(d, e))));
const cartesian = (a, b, ...c) => (b ? cartesian(f(a, b), ...c) : a);

/////////////////////////////////////////////////
///////////////////// PRINTERS //////////////////
/////////////////////////////////////////////////

const printN = N => `N: {${N.join(', ')}}`;;
const printΣ = Σ => `Σ: {${Σ.join(', ')}}`;;
const printRule = (r, k) => `    ${k} -> ${r}`;

const printP = P => {
  const rules = pipe(
    groupBy(nth(0)),
    map(map(tail)),
    map(map(join(''))),
    map(join('|'))
  )(P);
  
  const rulesStrings = pipe(
    mapObjIndexed(printRule),
    values,
    sort(sorter)
  )(rules);
  
  return `P: {\n${join(',\n', rulesStrings)}\n  }`;
};
const printS = S => `S: ${S}`;

const printG = G => {
  const N = printN(G.N);
  const Σ = printΣ(G.Σ);
  const P = printP(G.P);
  const S = printS(G.S);
  
  console.log(`(\n  ${N},\n  ${Σ},\n  ${P},\n  ${S}\n)`);
};

/////////////////////////////////////////////////
///////////////////// GRAMMAR TOOLS /////////////
/////////////////////////////////////////////////

const parseRule = pipe(
  map(split('')),
  flatten
);
const parseRules = map(parseRule);

const getNuΣ = pipe(
  flatten,
  uniq
);

const isUppercase = c => typeof c === 'string' && c[0] === c[0].toUpperCase();
const isLowercase = c => typeof c === 'string' && c[0] === c[0].toLowerCase();

const createN = filter(isUppercase);
const createΣ = pipe(
  reject(isUppercase),
  reject(equals(eps))
);

const createG = (P, S) => {
  const newP = parseRules(P); 
  const NuΣ = getNuΣ(newP);
  const N = createN(NuΣ);
  const Σ = createΣ(NuΣ);
     
  return {N, Σ, P: newP, S};
};

/////////////////////////////////////////////////
///////////////////// VETA 3.2 //////////////////
/////////////////////////////////////////////////

// veta 3.2 - 1
const criterium3_2_1 = ({rule}) => {
  const [_, X2, X3] = rule;
  
  if(rule.length === 2) {
     return X2 === eps;
  }
  
  if(rule.length === 3) {
     return isLowercase(X2) && isUppercase(X3);
  }
  
  return false;
};

const transformation3_2_1 = ({rule}) => {
  return {rule: [rule]};
};

// veta 3.2 - 2
const criterium3_2_2 = ({rule, index}) => {
  const l = last(rule);
      
  return isUppercase(l) && rule.length >= 3;
};

const generateNonterminals = (first, last, index, no) => pipe(
  range(0),
  mapObjIndexed((n,i) => `${first}_${index}_${i}`),
  values,
  prepend(first),
  append(last),
  map(nonterm => {
    if(nonterm === 'X_0_0') return 'U';
    if(nonterm === 'X_0_1') return 'V';
    if(nonterm === 'X_0_2') return 'W';
    if(nonterm === 'Y_4_0') return 'Z';
    
    return nonterm;
  })
)(no - 1);

const transformation3_2_2 = ({rule, index}) => {
  const baseNonterminal = head(rule);
  const lastNonterminal = last(rule);
  const terminals = reverse(tail(reverse(tail(rule))));
  const terminalsNo = terminals.length;
  
  const nonterminals = generateNonterminals(baseNonterminal, lastNonterminal, index, terminalsNo);
  const rightNonterminals = tail(nonterminals);
  const leftNonterminals = reverse(tail(reverse(nonterminals)))
  
  const rules = pipe(
    zip(__, terminals),
    zip(__, rightNonterminals),
    map(flatten)
  )(leftNonterminals);
    
  return {rule: rules};
};

// veta 3.2 - 3
const criterium3_2_3 = ({rule}) => {
  const l = last(rule);
        
  return isLowercase(l) && rule.length >= 2;
};

const transformation3_2_3 = ({rule, index}) => {
  const baseNonterminal = head(rule);
  const terminals = pipe(
    tail,
    append(eps)
  )(rule);
  const terminalsNo = terminals.length;
  
  const nonterminals = generateNonterminals(baseNonterminal, null, index, terminalsNo);
  const rightNonterminals = tail(nonterminals);
  const leftNonterminals = reverse(tail(reverse(nonterminals)))
    
  const rules = pipe(
    zip(__, terminals),
    zip(__, rightNonterminals),
    map(flatten),
    map(filter(identity))
  )(leftNonterminals);
  
  return {rule: rules};
};

// veta 3.2 - 4
const criterium3_2_4 = () => {};
const transformation3_2_4 = () => {};

// left linear -> left regular rules
const LLG_RuleToLRG_Rule = (rule, index) => pipe(
  when(criterium3_2_1, transformation3_2_1),
  when(criterium3_2_2, transformation3_2_2),
  when(criterium3_2_3, transformation3_2_3),
  when(({rule}) => isSimpleRule(rule), x => ({rule: [x.rule]})),
  prop('rule')
)({rule, index});

const transformG1Rules = pipe(
  mapObjIndexed(LLG_RuleToLRG_Rule),
  values,
  reduce(concat, [])
);

const toG1 = G => {
  const nP = transformG1Rules(G.P); 
  const newNuΣ = getNuΣ(nP);
  const nN = createN(newNuΣ);
  const nΣ = createΣ(newNuΣ);
  const newG = {N: nN, Σ: nΣ, P: nP, S: G.S};
        
  const simpleRules = filterSimpleRules(G.P);
    
  const nonterminalObj = zipObj(G.N, G.N);
  
  const findSetFor = Ni => pipe(
    filter(rule => {
      const B = head(rule);
      return contains(B, Ni);
    }),
    map(nth(1))
  )(simpleRules);
    
  const findNPlus1 = Ni => {
    const leftSide = findSetFor(Ni);
        
    return pipe(
      concat(Ni),
      uniq
    )(leftSide);
  };
  
  const findNFor = A => {
    const N0 = [A]; 
    const N1 = findNPlus1(N0);
    
    const data = {N: N0, NPlus1: N1};
    const NNotEquals = data => !equals(data.N, data.NPlus1);
    const f = data => ({
      N: data.NPlus1,
      NPlus1: findNPlus1(data.NPlus1)
    });
        
    const out = pipe(
      myUntil,
      prop('NPlus1')
    )(NNotEquals, f, data);
                
    return out;
  };
  
  const NA = map(findNFor, nonterminalObj);

  const findRules = B => {    
    const matchingRules = pipe(
      reject(isSimpleRule),
      filter(propSatisfies(equals(B), 0))
    )(newG.P);
    
    const As = filter(A => contains(B, NA[A]), keys(NA));
    
    const out = map(rule => {
      const rest = tail(rule);
      
      return map(A => prepend(A, rest), As);
    }, matchingRules);

    return reduce(concat, [], out);
  };
  
  const newRulesFrom3_2_4 = pipe(
    keys,
    map(findRules),
    values,
    reduce(concat, [])
  )(NA); 
    
  const newP = pipe(
    concat(newG.P),
    uniq,
    reject(isSimpleRule)
  )(newRulesFrom3_2_4);
        
  return {...newG, P: newP};
};

/////////////////////////////////////////////////
///////////////////// VETA 3.3 //////////////////
/////////////////////////////////////////////////

const isStringMadeOf = (s, chars) => all(contains(__, chars), s);

const satisfiesN1Cond = N => rule => {
  if(!isSimpleRule(rule)) {
    return false;
  }
  
  const A = head(rule);
  const B = last(rule);
  
  return contains(B, N);
};

const getNPlus1 = (N, P, Σ) => pipe(
  filter(satisfiesN1Cond(N)),
  map(head)
)(P);
  
const getNEps = G => {
  const P = G.P;
  const Σ = G.Σ;
  
  const N0 = [];
  const N1 = pipe(
    filterEpsRules,
    map(head)
  )(P);
      
  const cond = data => !equals(data.NMin1, data.N);
  const f = data => {
    const newN = pipe(
      getNPlus1,
      concat(data.N),
      uniq,
    )(data.N, P, Σ);
    
    return {
      NMin1: data.N,
      N: newN
    }
  };
  const data = {
    NMin1: N0,
    N: N1
  };
  
  return pipe(
    myUntil,
    prop('N'),
    uniq
  )(cond, f, data);
};

const getPosOfNEpsNonterms = (NEps, rule) => {
  const h = head(rule);
  const t = tail(rule);
  
  const x = mapObjIndexed((c, i) => (isUppercase(c) && contains(c, NEps)) ? parseInt(i, 10) : null,t);
  
  return pipe(
    values,
    prepend(null)
  )(x);
};

const replaceNontermsByTupple = rule => pipe(
  zip(rule),
  map(d => d[1] === eps ? eps : d[0]),
  removeEpsFromRule
);

const splitRule = (NEps, G) => rule => {
  const posOfNEpsNonterms = getPosOfNEpsNonterms(NEps, rule);
  const indicesTupples = pipe(
    map(i => [i, i !== null ? eps : null]),
    c => cartesian(...c),
    uniq
  )(posOfNEpsNonterms);
  
  const newRules = pipe(
    map(replaceNontermsByTupple(rule)),
    rejectEpsRules
  )(indicesTupples);
    
  return newRules;
};

const toGReg = G => {
  const NEps = getNEps(G);
  console.log(NEps);
  
  const nonEpsRules = rejectEpsRules(G.P);
  const nonTerminatingRules = rejectTerminatingRules(nonEpsRules);
   
  const newRules = pipe(
    map(splitRule(NEps, G)),
    reduce(concat, []),
    rejectEpsRules,
    map(removeEpsFromRule),
  )(nonTerminatingRules);
  
  const NEpsContainsS = contains(G.S, NEps);
  const newPotentialStart = G.S + '\'';
  const newS = NEpsContainsS ? newPotentialStart : G.S;
  
  const newNewRules = pipe(
    filterTerminatingRules,
    concat(newRules),
    //rejectEpsRules
  )(G.P);
  
  const newP = NEpsContainsS ? pipe(
    prepend([newPotentialStart, G.S]),
    prepend([newPotentialStart, eps]),
  )(newNewRules) : newNewRules;
  
  const newN = NEpsContainsS ? append(newPotentialStart, G.N) : G.N;
      
  return {
    N: newN,
    Σ: G.Σ,
    P: newP,
    S: newS
  }
};

/////////////////////////////////////////////////
///////////////////// GRAMMAR TO NKA ////////////
/////////////////////////////////////////////////

const ruleToTransition = rule => {
  const A = head(rule);
  const a = nth(1, rule);
  const B = pipe(
    nth(2),
    defaultTo('Qf')
  )(rule);
  
  return [A, a, B];
};

const GToNKA = G => {
  const Q = append('Qf', G.N);
  const Σ = G.Σ;

  const epsilonRule = filterEpsRules(G.P)[0];
  
  const simpleRules = filterSimpleRules(G.P);
  const simpleTransitions = map(sr => [sr[0], eps, sr[1]], simpleRules);
  
  const nonepsilonRules = pipe(
    rejectEpsRules,
    rejectSimpleRules
  )(G.P);
  const rules = map(ruleToTransition, nonepsilonRules);
  
  const q0 = G.S;
  const F = epsilonRule && epsilonRule[0] === G.S ? [G.S, 'Qf'] : ['Qf'];
  
  const R = [...simpleTransitions, ...rules];
  
  return {Q, Σ, R, q0, F};
};

/////////////////////////////////////////////////
///////////////////// REVERSED NKA //////////////
/////////////////////////////////////////////////

const ReverseNKA = M => {
  const newTransitions = map(f => (['Qs', eps, f]), M.F) 

  const Q = prepend('Qs', M.Q);
  const Σ = M.Σ;
  const R = pipe(
    map(reverse),
    concat(newTransitions)
  )(M.R);
  const q0 = 'Qs';
  const F = [M.q0];

  return {Q, Σ, R, q0, F};
};

/////////////////////////////////////////////////
///////////////////// NKA to LRG/////////////////
/////////////////////////////////////////////////

const NKAtoLRG = M => {
  const N = M.Q;
  const Σ = M.Σ;
  const S = M.q0;
  
  const rules = M.R;
  const addedRules = map(f => ([f, eps]), M.F);
  const P = concat(rules, addedRules);
      
  return {N, Σ, S, P};
};

/////////////////////////////////////////////////
///////////////////// REVERSE RULES /////////////
/////////////////////////////////////////////////

const ReverseRightRulesPart = G => {
  const P = map(rule => {
    const h = head(rule);
    const t = reverse(tail(rule));
    
    return [h, ...t];
  }, G.P);
    
  return {...G, P};
};

// pravá -> levá lineární gramatika

const N = [];
const Σ = [];

// [A, w, B]: A => w B;     A, B in N, w in Σ*
const P = [
  ['X', 'abc'],
  ['X', 'Y'],
  ['X', eps],
  ['Y', 'a', 'Y'],
  ['Y', 'cb', 'X'],
];

const S = 'X';
const RLG = createG(P, S);
const G1 = toG1(RLG);
const RRG = toGReg(G1);
const NKA = GToNKA(RRG);
const RNKA = ReverseNKA(NKA);
const LRG = NKAtoLRG(RNKA);
const RLRG = ReverseRightRulesPart(LRG);
const RLRGWithoutEps = toGReg(RLRG);

printG(RLRG);
printG(RLRGWithoutEps);