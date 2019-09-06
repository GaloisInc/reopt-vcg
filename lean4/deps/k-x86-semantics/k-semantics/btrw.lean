def btrw1 : instruction :=
  definst "btrw" $ do
    pattern fun (v_3235 : imm int) (v_3238 : reg (bv 16)) => do
      v_6084 <- getRegister v_3238;
      v_6087 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3235 8 8) (expression.bv_nat 8 15)) 16);
      setRegister (lhs.of_reg v_3238) (bv_and v_6084 (bv_xor (extract (shl (expression.bv_nat 16 1) v_6087) 0 16) (expression.bv_nat 16 65535)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6084 v_6087) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3242 : reg (bv 16)) (v_3243 : reg (bv 16)) => do
      v_6100 <- getRegister v_3243;
      v_6101 <- getRegister v_3242;
      v_6102 <- eval (bv_and v_6101 (expression.bv_nat 16 15));
      setRegister (lhs.of_reg v_3243) (bv_and v_6100 (bv_xor (extract (shl (expression.bv_nat 16 1) v_6102) 0 16) (expression.bv_nat 16 65535)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6100 v_6102) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3227 : imm int) (v_3230 : Mem) => do
      v_10670 <- evaluateAddress v_3230;
      v_10671 <- eval (handleImmediateWithSignExtend v_3227 8 8);
      v_10675 <- eval (add v_10670 (concat (expression.bv_nat 59 0) (bv_and (extract v_10671 0 5) (expression.bv_nat 5 1))));
      v_10676 <- load v_10675 1;
      v_10679 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10671 5 8) (expression.bv_nat 3 7)));
      store v_10675 (bv_and v_10676 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10679) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10676 v_10679) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3234 : reg (bv 16)) (v_3233 : Mem) => do
      v_10692 <- evaluateAddress v_3233;
      v_10693 <- getRegister v_3234;
      v_10697 <- eval (add v_10692 (concat (expression.bv_nat 3 0) (extract (sext v_10693 64) 0 61)));
      v_10698 <- load v_10697 1;
      v_10700 <- eval (concat (expression.bv_nat 5 0) (extract v_10693 13 16));
      store v_10697 (bv_and v_10698 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10700) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10698 v_10700) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
