def vpcmpgtq1 : instruction :=
  definst "vpcmpgtq" $ do
    pattern fun (v_2902 : reg (bv 128)) (v_2903 : reg (bv 128)) (v_2904 : reg (bv 128)) => do
      v_7956 <- getRegister v_2903;
      v_7958 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2904) (concat (mux (sgt (extract v_7956 0 64) (extract v_7958 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_7956 64 128) (extract v_7958 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2916 : reg (bv 256)) (v_2917 : reg (bv 256)) (v_2918 : reg (bv 256)) => do
      v_7973 <- getRegister v_2917;
      v_7975 <- getRegister v_2916;
      setRegister (lhs.of_reg v_2918) (concat (mux (sgt (extract v_7973 0 64) (extract v_7975 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_7973 64 128) (extract v_7975 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_7973 128 192) (extract v_7975 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_7973 192 256) (extract v_7975 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2901 : Mem) (v_2897 : reg (bv 128)) (v_2898 : reg (bv 128)) => do
      v_16772 <- getRegister v_2897;
      v_16774 <- evaluateAddress v_2901;
      v_16775 <- load v_16774 16;
      setRegister (lhs.of_reg v_2898) (concat (mux (sgt (extract v_16772 0 64) (extract v_16775 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_16772 64 128) (extract v_16775 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2910 : Mem) (v_2911 : reg (bv 256)) (v_2912 : reg (bv 256)) => do
      v_16785 <- getRegister v_2911;
      v_16787 <- evaluateAddress v_2910;
      v_16788 <- load v_16787 32;
      setRegister (lhs.of_reg v_2912) (concat (mux (sgt (extract v_16785 0 64) (extract v_16788 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_16785 64 128) (extract v_16788 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_16785 128 192) (extract v_16788 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_16785 192 256) (extract v_16788 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
