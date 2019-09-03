def btsl1 : instruction :=
  definst "btsl" $ do
    pattern fun (v_3177 : imm int) (v_3179 : reg (bv 32)) => do
      v_6521 <- getRegister v_3179;
      v_6526 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3177 8 8) (expression.bv_nat 8 31)))));
      setRegister (lhs.of_reg v_3179) (bv_or v_6521 (extract (shl (expression.bv_nat 32 1) v_6526) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6521 v_6526) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3183 : reg (bv 32)) (v_3184 : reg (bv 32)) => do
      v_6538 <- getRegister v_3184;
      v_6539 <- getRegister v_3183;
      v_6543 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and v_6539 (expression.bv_nat 32 31)))));
      setRegister (lhs.of_reg v_3184) (bv_or v_6538 (extract (shl (expression.bv_nat 32 1) v_6543) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6538 v_6543) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3170 : imm int) (v_3169 : Mem) => do
      v_11595 <- evaluateAddress v_3169;
      v_11596 <- eval (handleImmediateWithSignExtend v_3170 8 8);
      v_11600 <- eval (add v_11595 (concat (expression.bv_nat 59 0) (bv_and (extract v_11596 0 5) (expression.bv_nat 5 3))));
      v_11601 <- load v_11600 1;
      v_11605 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11596 5 8) (expression.bv_nat 3 7))));
      store v_11600 (bv_or v_11601 (extract (shl (expression.bv_nat 8 1) v_11605) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11601 v_11605) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3174 : reg (bv 32)) (v_3173 : Mem) => do
      v_11617 <- evaluateAddress v_3173;
      v_11618 <- getRegister v_3174;
      v_11622 <- eval (add v_11617 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_11618 64) 0 61)));
      v_11623 <- load v_11622 1;
      v_11626 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11618 29 32)));
      store v_11622 (bv_or v_11623 (extract (shl (expression.bv_nat 8 1) v_11626) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11623 v_11626) 7 8);
      pure ()
    pat_end
