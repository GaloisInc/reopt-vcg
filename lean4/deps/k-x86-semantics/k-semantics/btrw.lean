def btrw1 : instruction :=
  definst "btrw" $ do
    pattern fun (v_3159 : imm int) (v_3161 : reg (bv 16)) => do
      v_6477 <- getRegister v_3161;
      v_6482 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3159 8 8) (expression.bv_nat 8 15)))));
      setRegister (lhs.of_reg v_3161) (bv_and v_6477 (bv_xor (extract (shl (expression.bv_nat 16 1) v_6482) 0 16) (expression.bv_nat 16 65535)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6477 v_6482) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3165 : reg (bv 16)) (v_3166 : reg (bv 16)) => do
      v_6495 <- getRegister v_3166;
      v_6496 <- getRegister v_3165;
      v_6500 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and v_6496 (expression.bv_nat 16 15)))));
      setRegister (lhs.of_reg v_3166) (bv_and v_6495 (bv_xor (extract (shl (expression.bv_nat 16 1) v_6500) 0 16) (expression.bv_nat 16 65535)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6495 v_6500) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3152 : imm int) (v_3151 : Mem) => do
      v_11550 <- evaluateAddress v_3151;
      v_11551 <- eval (handleImmediateWithSignExtend v_3152 8 8);
      v_11555 <- eval (add v_11550 (concat (expression.bv_nat 59 0) (bv_and (extract v_11551 0 5) (expression.bv_nat 5 1))));
      v_11556 <- load v_11555 1;
      v_11560 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11551 5 8) (expression.bv_nat 3 7))));
      store v_11555 (bv_and v_11556 (bv_xor (extract (shl (expression.bv_nat 8 1) v_11560) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11556 v_11560) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3156 : reg (bv 16)) (v_3155 : Mem) => do
      v_11573 <- evaluateAddress v_3155;
      v_11574 <- getRegister v_3156;
      v_11578 <- eval (add v_11573 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_11574 64) 0 61)));
      v_11579 <- load v_11578 1;
      v_11582 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11574 13 16)));
      store v_11578 (bv_and v_11579 (bv_xor (extract (shl (expression.bv_nat 8 1) v_11582) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11579 v_11582) 7 8);
      pure ()
    pat_end
