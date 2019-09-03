def pinsrd1 : instruction :=
  definst "pinsrd" $ do
    pattern fun (v_2504 : imm int) (v_2505 : reg (bv 32)) (v_2503 : reg (bv 128)) => do
      v_4433 <- getRegister v_2503;
      v_4436 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2504 8 8) 6 8));
      v_4440 <- eval (uvalueMInt (extract (shl v_4436 5) 0 (bitwidthMInt v_4436)));
      v_4442 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_4440) 0 128);
      v_4447 <- getRegister v_2505;
      v_4448 <- eval (concat (expression.bv_nat 96 0) v_4447);
      setRegister (lhs.of_reg v_2503) (bv_or (bv_and v_4433 (bv_xor v_4442 (mi (bitwidthMInt v_4442) -1))) (bv_and (extract (shl v_4448 v_4440) 0 (bitwidthMInt v_4448)) v_4442));
      pure ()
    pat_end;
    pattern fun (v_2499 : imm int) (v_2497 : Mem) (v_2498 : reg (bv 128)) => do
      v_11871 <- getRegister v_2498;
      v_11874 <- eval (concat (expression.bv_nat 126 0) (extract (handleImmediateWithSignExtend v_2499 8 8) 6 8));
      v_11878 <- eval (uvalueMInt (extract (shl v_11874 5) 0 (bitwidthMInt v_11874)));
      v_11880 <- eval (extract (shl (expression.bv_nat 128 4294967295) v_11878) 0 128);
      v_11885 <- evaluateAddress v_2497;
      v_11886 <- load v_11885 4;
      v_11887 <- eval (concat (expression.bv_nat 96 0) v_11886);
      setRegister (lhs.of_reg v_2498) (bv_or (bv_and v_11871 (bv_xor v_11880 (mi (bitwidthMInt v_11880) -1))) (bv_and (extract (shl v_11887 v_11878) 0 (bitwidthMInt v_11887)) v_11880));
      pure ()
    pat_end
