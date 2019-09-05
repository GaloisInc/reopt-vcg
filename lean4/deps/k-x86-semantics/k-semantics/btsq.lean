def btsq1 : instruction :=
  definst "btsq" $ do
    pattern fun (v_3245 : imm int) (v_3248 : reg (bv 64)) => do
      v_6279 <- getRegister v_3248;
      v_6282 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3245 8 8) (expression.bv_nat 8 63)) 64);
      setRegister (lhs.of_reg v_3248) (bv_or v_6279 (extract (shl (expression.bv_nat 64 1) v_6282) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6279 v_6282) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3252 : reg (bv 64)) (v_3253 : reg (bv 64)) => do
      v_6294 <- getRegister v_3253;
      v_6295 <- getRegister v_3252;
      v_6296 <- eval (bv_and v_6295 (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_3253) (bv_or v_6294 (extract (shl (expression.bv_nat 64 1) v_6296) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6294 v_6296) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3237 : imm int) (v_3239 : Mem) => do
      v_11030 <- evaluateAddress v_3239;
      v_11031 <- eval (handleImmediateWithSignExtend v_3237 8 8);
      v_11035 <- eval (add v_11030 (concat (expression.bv_nat 59 0) (bv_and (extract v_11031 0 5) (expression.bv_nat 5 7))));
      v_11036 <- load v_11035 1;
      v_11039 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_11031 5 8) (expression.bv_nat 3 7)));
      store v_11035 (bv_or v_11036 (extract (shl (expression.bv_nat 8 1) v_11039) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_11036 v_11039) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3243 : reg (bv 64)) (v_3242 : Mem) => do
      v_11051 <- evaluateAddress v_3242;
      v_11052 <- getRegister v_3243;
      v_11055 <- eval (add v_11051 (concat (expression.bv_nat 3 0) (extract v_11052 0 61)));
      v_11056 <- load v_11055 1;
      v_11058 <- eval (concat (expression.bv_nat 5 0) (extract v_11052 61 64));
      store v_11055 (bv_or v_11056 (extract (shl (expression.bv_nat 8 1) v_11058) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_11056 v_11058) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
