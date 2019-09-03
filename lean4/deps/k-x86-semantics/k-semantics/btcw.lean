def btcw1 : instruction :=
  definst "btcw" $ do
    pattern fun (v_3069 : imm int) (v_3071 : reg (bv 16)) => do
      v_6279 <- getRegister v_3071;
      v_6284 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3069 8 8) (expression.bv_nat 8 15)))));
      setRegister (lhs.of_reg v_3071) (bv_xor v_6279 (extract (shl (expression.bv_nat 16 1) v_6284) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6279 v_6284) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3075 : reg (bv 16)) (v_3076 : reg (bv 16)) => do
      v_6296 <- getRegister v_3076;
      v_6297 <- getRegister v_3075;
      v_6301 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and v_6297 (expression.bv_nat 16 15)))));
      setRegister (lhs.of_reg v_3076) (bv_xor v_6296 (extract (shl (expression.bv_nat 16 1) v_6301) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6296 v_6301) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3062 : imm int) (v_3061 : Mem) => do
      v_11418 <- evaluateAddress v_3061;
      v_11419 <- eval (handleImmediateWithSignExtend v_3062 8 8);
      v_11423 <- eval (add v_11418 (concat (expression.bv_nat 59 0) (bv_and (extract v_11419 0 5) (expression.bv_nat 5 1))));
      v_11424 <- load v_11423 1;
      v_11428 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11419 5 8) (expression.bv_nat 3 7))));
      store v_11423 (bv_xor v_11424 (extract (shl (expression.bv_nat 8 1) v_11428) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11424 v_11428) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3066 : reg (bv 16)) (v_3065 : Mem) => do
      v_11440 <- evaluateAddress v_3065;
      v_11441 <- getRegister v_3066;
      v_11445 <- eval (add v_11440 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_11441 64) 0 61)));
      v_11446 <- load v_11445 1;
      v_11449 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11441 13 16)));
      store v_11445 (bv_xor v_11446 (extract (shl (expression.bv_nat 8 1) v_11449) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11446 v_11449) 7 8);
      pure ()
    pat_end
