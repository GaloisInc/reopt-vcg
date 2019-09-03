def vpcmpgtd1 : instruction :=
  definst "vpcmpgtd" $ do
    pattern fun (v_2870 : reg (bv 128)) (v_2871 : reg (bv 128)) (v_2872 : reg (bv 128)) => do
      v_8019 <- getRegister v_2871;
      v_8021 <- getRegister v_2870;
      setRegister (lhs.of_reg v_2872) (concat (mux (sgt (extract v_8019 0 32) (extract v_8021 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8019 32 64) (extract v_8021 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8019 64 96) (extract v_8021 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_8019 96 128) (extract v_8021 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2881 : reg (bv 256)) (v_2882 : reg (bv 256)) (v_2883 : reg (bv 256)) => do
      v_8046 <- getRegister v_2882;
      v_8048 <- getRegister v_2881;
      setRegister (lhs.of_reg v_2883) (concat (mux (sgt (extract v_8046 0 32) (extract v_8048 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8046 32 64) (extract v_8048 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8046 64 96) (extract v_8048 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8046 96 128) (extract v_8048 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8046 128 160) (extract v_8048 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8046 160 192) (extract v_8048 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_8046 192 224) (extract v_8048 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_8046 224 256) (extract v_8048 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2864 : Mem) (v_2865 : reg (bv 128)) (v_2866 : reg (bv 128)) => do
      v_17215 <- getRegister v_2865;
      v_17217 <- evaluateAddress v_2864;
      v_17218 <- load v_17217 16;
      setRegister (lhs.of_reg v_2866) (concat (mux (sgt (extract v_17215 0 32) (extract v_17218 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17215 32 64) (extract v_17218 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17215 64 96) (extract v_17218 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_17215 96 128) (extract v_17218 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2875 : Mem) (v_2876 : reg (bv 256)) (v_2877 : reg (bv 256)) => do
      v_17238 <- getRegister v_2876;
      v_17240 <- evaluateAddress v_2875;
      v_17241 <- load v_17240 32;
      setRegister (lhs.of_reg v_2877) (concat (mux (sgt (extract v_17238 0 32) (extract v_17241 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17238 32 64) (extract v_17241 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17238 64 96) (extract v_17241 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17238 96 128) (extract v_17241 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17238 128 160) (extract v_17241 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17238 160 192) (extract v_17241 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_17238 192 224) (extract v_17241 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_17238 224 256) (extract v_17241 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
