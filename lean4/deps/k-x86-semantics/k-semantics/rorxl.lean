def rorxl1 : instruction :=
  definst "rorxl" $ do
    pattern fun (v_2841 : imm int) (v_2843 : reg (bv 32)) (v_2844 : reg (bv 32)) => do
      v_5462 <- getRegister v_2843;
      v_5465 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2841 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2844) (bv_or (lshr v_5462 v_5465) (extract (shl v_5462 (sub (expression.bv_nat 32 32) v_5465)) 0 32));
      pure ()
    pat_end;
    pattern fun (v_2831 : imm int) (v_2832 : Mem) (v_2833 : reg (bv 32)) => do
      v_11236 <- evaluateAddress v_2832;
      v_11237 <- load v_11236 4;
      v_11240 <- eval (bv_and (concat (expression.bv_nat 24 0) (handleImmediateWithSignExtend v_2831 8 8)) (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_2833) (bv_or (lshr v_11237 v_11240) (extract (shl v_11237 (sub (expression.bv_nat 32 32) v_11240)) 0 32));
      pure ()
    pat_end
