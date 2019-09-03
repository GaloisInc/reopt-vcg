def vpcmpgtq1 : instruction :=
  definst "vpcmpgtq" $ do
    pattern fun (v_2892 : reg (bv 128)) (v_2893 : reg (bv 128)) (v_2894 : reg (bv 128)) => do
      v_8093 <- getRegister v_2893;
      v_8095 <- getRegister v_2892;
      setRegister (lhs.of_reg v_2894) (concat (mux (sgt (extract v_8093 0 64) (extract v_8095 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_8093 64 128) (extract v_8095 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2903 : reg (bv 256)) (v_2904 : reg (bv 256)) (v_2905 : reg (bv 256)) => do
      v_8110 <- getRegister v_2904;
      v_8112 <- getRegister v_2903;
      setRegister (lhs.of_reg v_2905) (concat (mux (sgt (extract v_8110 0 64) (extract v_8112 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_8110 64 128) (extract v_8112 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_8110 128 192) (extract v_8112 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_8110 192 256) (extract v_8112 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2886 : Mem) (v_2887 : reg (bv 128)) (v_2888 : reg (bv 128)) => do
      v_17281 <- getRegister v_2887;
      v_17283 <- evaluateAddress v_2886;
      v_17284 <- load v_17283 16;
      setRegister (lhs.of_reg v_2888) (concat (mux (sgt (extract v_17281 0 64) (extract v_17284 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_17281 64 128) (extract v_17284 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2897 : Mem) (v_2898 : reg (bv 256)) (v_2899 : reg (bv 256)) => do
      v_17294 <- getRegister v_2898;
      v_17296 <- evaluateAddress v_2897;
      v_17297 <- load v_17296 32;
      setRegister (lhs.of_reg v_2899) (concat (mux (sgt (extract v_17294 0 64) (extract v_17297 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_17294 64 128) (extract v_17297 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (sgt (extract v_17294 128 192) (extract v_17297 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_17294 192 256) (extract v_17297 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
