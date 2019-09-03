def btsw1 : instruction :=
  definst "btsw" $ do
    pattern fun (v_3199 : imm int) (v_3202 : reg (bv 16)) => do
      v_6462 <- getRegister v_3202;
      v_6467 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3199 8 8) (expression.bv_nat 8 15)))));
      setRegister (lhs.of_reg v_3202) (bv_or v_6462 (extract (shl (expression.bv_nat 16 1) v_6467) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6462 v_6467) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3206 : reg (bv 16)) (v_3207 : reg (bv 16)) => do
      v_6479 <- getRegister v_3207;
      v_6480 <- getRegister v_3206;
      v_6484 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and v_6480 (expression.bv_nat 16 15)))));
      setRegister (lhs.of_reg v_3207) (bv_or v_6479 (extract (shl (expression.bv_nat 16 1) v_6484) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6479 v_6484) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3191 : imm int) (v_3193 : Mem) => do
      v_11414 <- evaluateAddress v_3193;
      v_11415 <- eval (handleImmediateWithSignExtend v_3191 8 8);
      v_11419 <- eval (add v_11414 (concat (expression.bv_nat 59 0) (bv_and (extract v_11415 0 5) (expression.bv_nat 5 1))));
      v_11420 <- load v_11419 1;
      v_11424 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11415 5 8) (expression.bv_nat 3 7))));
      store v_11419 (bv_or v_11420 (extract (shl (expression.bv_nat 8 1) v_11424) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11420 v_11424) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3197 : reg (bv 16)) (v_3196 : Mem) => do
      v_11436 <- evaluateAddress v_3196;
      v_11437 <- getRegister v_3197;
      v_11442 <- eval (add v_11436 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_11437)) 0 61)));
      v_11443 <- load v_11442 1;
      v_11446 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11437 13 16)));
      store v_11442 (bv_or v_11443 (extract (shl (expression.bv_nat 8 1) v_11446) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11443 v_11446) 7 8);
      pure ()
    pat_end
