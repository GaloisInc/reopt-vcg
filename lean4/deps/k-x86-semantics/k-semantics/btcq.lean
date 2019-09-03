def btcq1 : instruction :=
  definst "btcq" $ do
    pattern fun (v_3051 : imm int) (v_3053 : reg (bv 64)) => do
      v_6237 <- getRegister v_3053;
      v_6242 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3051 8 8) (expression.bv_nat 8 63)))));
      setRegister (lhs.of_reg v_3053) (bv_xor v_6237 (extract (shl (expression.bv_nat 64 1) v_6242) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6237 v_6242) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3057 : reg (bv 64)) (v_3058 : reg (bv 64)) => do
      v_6254 <- getRegister v_3058;
      v_6255 <- getRegister v_3057;
      v_6259 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and v_6255 (expression.bv_nat 64 63)))));
      setRegister (lhs.of_reg v_3058) (bv_xor v_6254 (extract (shl (expression.bv_nat 64 1) v_6259) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6254 v_6259) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3044 : imm int) (v_3043 : Mem) => do
      v_11376 <- evaluateAddress v_3043;
      v_11377 <- eval (handleImmediateWithSignExtend v_3044 8 8);
      v_11381 <- eval (add v_11376 (concat (expression.bv_nat 59 0) (bv_and (extract v_11377 0 5) (expression.bv_nat 5 7))));
      v_11382 <- load v_11381 1;
      v_11386 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11377 5 8) (expression.bv_nat 3 7))));
      store v_11381 (bv_xor v_11382 (extract (shl (expression.bv_nat 8 1) v_11386) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11382 v_11386) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3048 : reg (bv 64)) (v_3047 : Mem) => do
      v_11398 <- evaluateAddress v_3047;
      v_11399 <- getRegister v_3048;
      v_11402 <- eval (add v_11398 (concat (expression.bv_nat 3 0) (extract v_11399 0 61)));
      v_11403 <- load v_11402 1;
      v_11406 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11399 61 64)));
      store v_11402 (bv_xor v_11403 (extract (shl (expression.bv_nat 8 1) v_11406) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11403 v_11406) 7 8);
      pure ()
    pat_end
