def shlx1 : instruction :=
  definst "shlx" $ do
    pattern fun (v_2916 : reg (bv 32)) (v_2917 : reg (bv 32)) (v_2918 : reg (bv 32)) => do
      v_6421 <- getRegister v_2917;
      v_6422 <- getRegister v_2916;
      setRegister (lhs.of_reg v_2918) (extract (shl v_6421 (bv_and v_6422 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2937 : reg (bv 64)) (v_2938 : reg (bv 64)) (v_2939 : reg (bv 64)) => do
      v_6438 <- getRegister v_2938;
      v_6439 <- getRegister v_2937;
      setRegister (lhs.of_reg v_2939) (extract (shl v_6438 (bv_and v_6439 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_2906 : reg (bv 32)) (v_2908 : Mem) (v_2907 : reg (bv 32)) => do
      v_9300 <- evaluateAddress v_2908;
      v_9301 <- load v_9300 4;
      v_9302 <- getRegister v_2906;
      setRegister (lhs.of_reg v_2907) (extract (shl v_9301 (bv_and v_9302 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2928 : reg (bv 64)) (v_2927 : Mem) (v_2929 : reg (bv 64)) => do
      v_9307 <- evaluateAddress v_2927;
      v_9308 <- load v_9307 8;
      v_9309 <- getRegister v_2928;
      setRegister (lhs.of_reg v_2929) (extract (shl v_9308 (bv_and v_9309 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end
