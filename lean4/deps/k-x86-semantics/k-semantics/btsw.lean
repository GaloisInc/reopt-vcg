def btsw1 : instruction :=
  definst "btsw" $ do
    pattern fun (v_3213 : imm int) (v_3215 : reg (bv 16)) => do
      v_6605 <- getRegister v_3215;
      v_6610 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3213 8 8) (expression.bv_nat 8 15)))));
      setRegister (lhs.of_reg v_3215) (bv_or v_6605 (extract (shl (expression.bv_nat 16 1) v_6610) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6605 v_6610) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3219 : reg (bv 16)) (v_3220 : reg (bv 16)) => do
      v_6622 <- getRegister v_3220;
      v_6623 <- getRegister v_3219;
      v_6627 <- eval (uvalueMInt (mi 16 (svalueMInt (bv_and v_6623 (expression.bv_nat 16 15)))));
      setRegister (lhs.of_reg v_3220) (bv_or v_6622 (extract (shl (expression.bv_nat 16 1) v_6627) 0 16));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6622 v_6627) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3206 : imm int) (v_3205 : Mem) => do
      v_11680 <- evaluateAddress v_3205;
      v_11681 <- eval (handleImmediateWithSignExtend v_3206 8 8);
      v_11685 <- eval (add v_11680 (concat (expression.bv_nat 59 0) (bv_and (extract v_11681 0 5) (expression.bv_nat 5 1))));
      v_11686 <- load v_11685 1;
      v_11690 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11681 5 8) (expression.bv_nat 3 7))));
      store v_11685 (bv_or v_11686 (extract (shl (expression.bv_nat 8 1) v_11690) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11686 v_11690) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3210 : reg (bv 16)) (v_3209 : Mem) => do
      v_11702 <- evaluateAddress v_3209;
      v_11703 <- getRegister v_3210;
      v_11707 <- eval (add v_11702 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_11703 64) 0 61)));
      v_11708 <- load v_11707 1;
      v_11711 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11703 13 16)));
      store v_11707 (bv_or v_11708 (extract (shl (expression.bv_nat 8 1) v_11711) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11708 v_11711) 7 8);
      pure ()
    pat_end
