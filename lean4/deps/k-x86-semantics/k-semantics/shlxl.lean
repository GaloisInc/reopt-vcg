def shlxl1 : instruction :=
  definst "shlxl" $ do
    pattern fun (v_2894 : reg (bv 32)) (v_2895 : reg (bv 32)) (v_2896 : reg (bv 32)) => do
      v_5130 <- getRegister v_2895;
      v_5131 <- getRegister v_2894;
      setRegister (lhs.of_reg v_2896) (extract (shl v_5130 (bv_and v_5131 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2884 : reg (bv 32)) (v_2883 : Mem) (v_2885 : reg (bv 32)) => do
      v_9021 <- evaluateAddress v_2883;
      v_9022 <- load v_9021 4;
      v_9023 <- getRegister v_2884;
      setRegister (lhs.of_reg v_2885) (extract (shl v_9022 (bv_and v_9023 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end
