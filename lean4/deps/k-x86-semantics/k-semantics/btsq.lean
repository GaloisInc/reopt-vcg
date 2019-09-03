def btsq1 : instruction :=
  definst "btsq" $ do
    pattern fun (v_3195 : imm int) (v_3197 : reg (bv 64)) => do
      v_6563 <- getRegister v_3197;
      v_6568 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3195 8 8) (expression.bv_nat 8 63)))));
      setRegister (lhs.of_reg v_3197) (bv_or v_6563 (extract (shl (expression.bv_nat 64 1) v_6568) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6563 v_6568) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3201 : reg (bv 64)) (v_3202 : reg (bv 64)) => do
      v_6580 <- getRegister v_3202;
      v_6581 <- getRegister v_3201;
      v_6585 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and v_6581 (expression.bv_nat 64 63)))));
      setRegister (lhs.of_reg v_3202) (bv_or v_6580 (extract (shl (expression.bv_nat 64 1) v_6585) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6580 v_6585) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3188 : imm int) (v_3187 : Mem) => do
      v_11638 <- evaluateAddress v_3187;
      v_11639 <- eval (handleImmediateWithSignExtend v_3188 8 8);
      v_11643 <- eval (add v_11638 (concat (expression.bv_nat 59 0) (bv_and (extract v_11639 0 5) (expression.bv_nat 5 7))));
      v_11644 <- load v_11643 1;
      v_11648 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11639 5 8) (expression.bv_nat 3 7))));
      store v_11643 (bv_or v_11644 (extract (shl (expression.bv_nat 8 1) v_11648) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11644 v_11648) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3192 : reg (bv 64)) (v_3191 : Mem) => do
      v_11660 <- evaluateAddress v_3191;
      v_11661 <- getRegister v_3192;
      v_11664 <- eval (add v_11660 (concat (expression.bv_nat 3 0) (extract v_11661 0 61)));
      v_11665 <- load v_11664 1;
      v_11668 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11661 61 64)));
      store v_11664 (bv_or v_11665 (extract (shl (expression.bv_nat 8 1) v_11668) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11665 v_11668) 7 8);
      pure ()
    pat_end
