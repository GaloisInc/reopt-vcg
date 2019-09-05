def vpcmpgtd1 : instruction :=
  definst "vpcmpgtd" $ do
    pattern fun (v_2934 : reg (bv 128)) (v_2935 : reg (bv 128)) (v_2936 : reg (bv 128)) => do
      v_7783 <- getRegister v_2935;
      v_7785 <- getRegister v_2934;
      setRegister (lhs.of_reg v_2936) (concat (mux (sgt (extract v_7783 0 32) (extract v_7785 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7783 32 64) (extract v_7785 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7783 64 96) (extract v_7785 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_7783 96 128) (extract v_7785 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2944 : reg (bv 256)) (v_2945 : reg (bv 256)) (v_2946 : reg (bv 256)) => do
      v_7810 <- getRegister v_2945;
      v_7812 <- getRegister v_2944;
      setRegister (lhs.of_reg v_2946) (concat (mux (sgt (extract v_7810 0 32) (extract v_7812 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 32 64) (extract v_7812 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 64 96) (extract v_7812 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 96 128) (extract v_7812 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 128 160) (extract v_7812 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 160 192) (extract v_7812 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 192 224) (extract v_7812 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_7810 224 256) (extract v_7812 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2928 : Mem) (v_2929 : reg (bv 128)) (v_2930 : reg (bv 128)) => do
      v_16359 <- getRegister v_2929;
      v_16361 <- evaluateAddress v_2928;
      v_16362 <- load v_16361 16;
      setRegister (lhs.of_reg v_2930) (concat (mux (sgt (extract v_16359 0 32) (extract v_16362 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16359 32 64) (extract v_16362 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16359 64 96) (extract v_16362 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_16359 96 128) (extract v_16362 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2939 : Mem) (v_2940 : reg (bv 256)) (v_2941 : reg (bv 256)) => do
      v_16382 <- getRegister v_2940;
      v_16384 <- evaluateAddress v_2939;
      v_16385 <- load v_16384 32;
      setRegister (lhs.of_reg v_2941) (concat (mux (sgt (extract v_16382 0 32) (extract v_16385 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16382 32 64) (extract v_16385 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16382 64 96) (extract v_16385 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16382 96 128) (extract v_16385 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16382 128 160) (extract v_16385 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16382 160 192) (extract v_16385 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16382 192 224) (extract v_16385 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_16382 224 256) (extract v_16385 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
