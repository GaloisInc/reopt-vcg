def vpcmpgtd1 : instruction :=
  definst "vpcmpgtd" $ do
    pattern fun (v_2880 : reg (bv 128)) (v_2881 : reg (bv 128)) (v_2882 : reg (bv 128)) => do
      v_7882 <- getRegister v_2881;
      v_7884 <- getRegister v_2880;
      setRegister (lhs.of_reg v_2882) (concat (mux (sgt (extract v_7882 0 32) (extract v_7884 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7882 32 64) (extract v_7884 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7882 64 96) (extract v_7884 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_7882 96 128) (extract v_7884 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2894 : reg (bv 256)) (v_2895 : reg (bv 256)) (v_2896 : reg (bv 256)) => do
      v_7909 <- getRegister v_2895;
      v_7911 <- getRegister v_2894;
      setRegister (lhs.of_reg v_2896) (concat (mux (sgt (extract v_7909 0 32) (extract v_7911 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7909 32 64) (extract v_7911 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7909 64 96) (extract v_7911 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7909 96 128) (extract v_7911 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7909 128 160) (extract v_7911 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7909 160 192) (extract v_7911 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7909 192 224) (extract v_7911 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_7909 224 256) (extract v_7911 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2879 : Mem) (v_2875 : reg (bv 128)) (v_2876 : reg (bv 128)) => do
      v_16706 <- getRegister v_2875;
      v_16708 <- evaluateAddress v_2879;
      v_16709 <- load v_16708 16;
      setRegister (lhs.of_reg v_2876) (concat (mux (sgt (extract v_16706 0 32) (extract v_16709 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16706 32 64) (extract v_16709 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16706 64 96) (extract v_16709 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_16706 96 128) (extract v_16709 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2888 : Mem) (v_2889 : reg (bv 256)) (v_2890 : reg (bv 256)) => do
      v_16729 <- getRegister v_2889;
      v_16731 <- evaluateAddress v_2888;
      v_16732 <- load v_16731 32;
      setRegister (lhs.of_reg v_2890) (concat (mux (sgt (extract v_16729 0 32) (extract v_16732 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16729 32 64) (extract v_16732 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16729 64 96) (extract v_16732 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16729 96 128) (extract v_16732 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16729 128 160) (extract v_16732 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16729 160 192) (extract v_16732 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16729 192 224) (extract v_16732 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_16729 224 256) (extract v_16732 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
