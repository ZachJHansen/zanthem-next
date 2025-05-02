anthem verify --equivalence strong p.{1.lp,2.lp} -t 10 --save-problems ./

cd infinite-models
source .venv/bin/activate
fest <path to countermodel.smt2>
