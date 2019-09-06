def vpcmpeqd1 : instruction :=
  definst "vpcmpeqd" $ do
    pattern fun (v_2872 : reg (bv 128)) (v_2873 : reg (bv 128)) (v_2874 : reg (bv 128)) => do
      v_7304 <- getRegister v_2873;
      v_7306 <- getRegister v_2872;
      setRegister (lhs.of_reg v_2874) (concat (mux (eq (extract v_7304 0 32) (extract v_7306 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 32 64) (extract v_7306 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 64 96) (extract v_7306 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7304 96 128) (extract v_7306 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2883 : reg (bv 256)) (v_2884 : reg (bv 256)) (v_2885 : reg (bv 256)) => do
      v_7331 <- getRegister v_2884;
      v_7333 <- getRegister v_2883;
      setRegister (lhs.of_reg v_2885) (concat (mux (eq (extract v_7331 0 32) (extract v_7333 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7331 32 64) (extract v_7333 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7331 64 96) (extract v_7333 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7331 96 128) (extract v_7333 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7331 128 160) (extract v_7333 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7331 160 192) (extract v_7333 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7331 192 224) (extract v_7333 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7331 224 256) (extract v_7333 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2867 : Mem) (v_2868 : reg (bv 128)) (v_2869 : reg (bv 128)) => do
      v_15912 <- getRegister v_2868;
      v_15914 <- evaluateAddress v_2867;
      v_15915 <- load v_15914 16;
      setRegister (lhs.of_reg v_2869) (concat (mux (eq (extract v_15912 0 32) (extract v_15915 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15912 32 64) (extract v_15915 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15912 64 96) (extract v_15915 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_15912 96 128) (extract v_15915 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2878 : Mem) (v_2879 : reg (bv 256)) (v_2880 : reg (bv 256)) => do
      v_15935 <- getRegister v_2879;
      v_15937 <- evaluateAddress v_2878;
      v_15938 <- load v_15937 32;
      setRegister (lhs.of_reg v_2880) (concat (mux (eq (extract v_15935 0 32) (extract v_15938 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15935 32 64) (extract v_15938 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15935 64 96) (extract v_15938 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15935 96 128) (extract v_15938 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15935 128 160) (extract v_15938 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15935 160 192) (extract v_15938 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15935 192 224) (extract v_15938 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_15935 224 256) (extract v_15938 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
