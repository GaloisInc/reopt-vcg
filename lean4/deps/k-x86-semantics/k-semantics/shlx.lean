def shlx1 : instruction :=
  definst "shlx" $ do
    pattern fun (v_2888 : reg (bv 32)) (v_2889 : reg (bv 32)) (v_2890 : reg (bv 32)) => do
      v_6982 <- getRegister v_2889;
      v_6983 <- getRegister v_2888;
      setRegister (lhs.of_reg v_2890) (extract (shl v_6982 (bv_and v_6983 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2909 : reg (bv 64)) (v_2910 : reg (bv 64)) (v_2911 : reg (bv 64)) => do
      v_6999 <- getRegister v_2910;
      v_7000 <- getRegister v_2909;
      setRegister (lhs.of_reg v_2911) (extract (shl v_6999 (bv_and v_7000 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_2879 : reg (bv 32)) (v_2878 : Mem) (v_2880 : reg (bv 32)) => do
      v_10104 <- evaluateAddress v_2878;
      v_10105 <- load v_10104 4;
      v_10106 <- getRegister v_2879;
      setRegister (lhs.of_reg v_2880) (extract (shl v_10105 (bv_and v_10106 (expression.bv_nat 32 31))) 0 32);
      pure ()
    pat_end;
    pattern fun (v_2900 : reg (bv 64)) (v_2899 : Mem) (v_2901 : reg (bv 64)) => do
      v_10111 <- evaluateAddress v_2899;
      v_10112 <- load v_10111 8;
      v_10113 <- getRegister v_2900;
      setRegister (lhs.of_reg v_2901) (extract (shl v_10112 (bv_and v_10113 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end
