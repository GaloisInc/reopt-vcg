def shlxl1 : instruction :=
  definst "shlxl" $ do
    pattern fun (v_2921 : reg (bv 32)) (v_2922 : reg (bv 32)) (v_2923 : reg (bv 32)) => do
      v_4825 <- getRegister v_2922;
      v_4826 <- getRegister v_2921;
      setRegister (lhs.of_reg v_2923) (extract (shl v_4825 (bv_and v_4826 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2912 : reg (bv 32)) (v_2911 : Mem) (v_2913 : reg (bv 32)) => do
      v_8414 <- evaluateAddress v_2911;
      v_8415 <- load v_8414 4;
      v_8416 <- getRegister v_2912;
      setRegister (lhs.of_reg v_2913) (extract (shl v_8415 (bv_and v_8416 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end
