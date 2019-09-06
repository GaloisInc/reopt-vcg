def shlxq1 : instruction :=
  definst "shlxq" $ do
    pattern fun (v_2942 : reg (bv 64)) (v_2943 : reg (bv 64)) (v_2944 : reg (bv 64)) => do
      v_4841 <- getRegister v_2943;
      v_4842 <- getRegister v_2942;
      setRegister (lhs.of_reg v_2944) (extract (shl v_4841 (bv_and v_4842 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end;
    pattern fun (v_2933 : reg (bv 64)) (v_2932 : Mem) (v_2934 : reg (bv 64)) => do
      v_8422 <- evaluateAddress v_2932;
      v_8423 <- load v_8422 8;
      v_8424 <- getRegister v_2933;
      setRegister (lhs.of_reg v_2934) (extract (shl v_8423 (bv_and v_8424 (expression.bv_nat 64 63))) 0 64);
      pure ()
    pat_end
