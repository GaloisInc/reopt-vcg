def btrq1 : instruction :=
  definst "btrq" $ do
    pattern fun (v_3141 : imm int) (v_3143 : reg (bv 64)) => do
      v_6433 <- getRegister v_3143;
      v_6438 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3141 8 8) (expression.bv_nat 8 63)))));
      setRegister (lhs.of_reg v_3143) (bv_and v_6433 (bv_xor (extract (shl (expression.bv_nat 64 1) v_6438) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6433 v_6438) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3147 : reg (bv 64)) (v_3148 : reg (bv 64)) => do
      v_6451 <- getRegister v_3148;
      v_6452 <- getRegister v_3147;
      v_6456 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and v_6452 (expression.bv_nat 64 63)))));
      setRegister (lhs.of_reg v_3148) (bv_and v_6451 (bv_xor (extract (shl (expression.bv_nat 64 1) v_6456) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6451 v_6456) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3134 : imm int) (v_3133 : Mem) => do
      v_11506 <- evaluateAddress v_3133;
      v_11507 <- eval (handleImmediateWithSignExtend v_3134 8 8);
      v_11511 <- eval (add v_11506 (concat (expression.bv_nat 59 0) (bv_and (extract v_11507 0 5) (expression.bv_nat 5 7))));
      v_11512 <- load v_11511 1;
      v_11516 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11507 5 8) (expression.bv_nat 3 7))));
      store v_11511 (bv_and v_11512 (bv_xor (extract (shl (expression.bv_nat 8 1) v_11516) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11512 v_11516) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3138 : reg (bv 64)) (v_3137 : Mem) => do
      v_11529 <- evaluateAddress v_3137;
      v_11530 <- getRegister v_3138;
      v_11533 <- eval (add v_11529 (concat (expression.bv_nat 3 0) (extract v_11530 0 61)));
      v_11534 <- load v_11533 1;
      v_11537 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11530 61 64)));
      store v_11533 (bv_and v_11534 (bv_xor (extract (shl (expression.bv_nat 8 1) v_11537) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11534 v_11537) 7 8);
      pure ()
    pat_end
