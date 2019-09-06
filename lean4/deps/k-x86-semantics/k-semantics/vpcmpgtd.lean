def vpcmpgtd1 : instruction :=
  definst "vpcmpgtd" $ do
    pattern fun (v_2960 : reg (bv 128)) (v_2961 : reg (bv 128)) (v_2962 : reg (bv 128)) => do
      v_7810 <- getRegister v_2961;
      v_7812 <- getRegister v_2960;
      setRegister (lhs.of_reg v_2962) (concat (mux (sgt (extract v_7810 0 32) (extract v_7812 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 32 64) (extract v_7812 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7810 64 96) (extract v_7812 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_7810 96 128) (extract v_7812 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2971 : reg (bv 256)) (v_2972 : reg (bv 256)) (v_2973 : reg (bv 256)) => do
      v_7837 <- getRegister v_2972;
      v_7839 <- getRegister v_2971;
      setRegister (lhs.of_reg v_2973) (concat (mux (sgt (extract v_7837 0 32) (extract v_7839 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7837 32 64) (extract v_7839 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7837 64 96) (extract v_7839 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7837 96 128) (extract v_7839 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7837 128 160) (extract v_7839 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7837 160 192) (extract v_7839 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_7837 192 224) (extract v_7839 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_7837 224 256) (extract v_7839 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) (v_2956 : reg (bv 128)) (v_2957 : reg (bv 128)) => do
      v_16386 <- getRegister v_2956;
      v_16388 <- evaluateAddress v_2955;
      v_16389 <- load v_16388 16;
      setRegister (lhs.of_reg v_2957) (concat (mux (sgt (extract v_16386 0 32) (extract v_16389 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16386 32 64) (extract v_16389 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16386 64 96) (extract v_16389 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_16386 96 128) (extract v_16389 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2966 : Mem) (v_2967 : reg (bv 256)) (v_2968 : reg (bv 256)) => do
      v_16409 <- getRegister v_2967;
      v_16411 <- evaluateAddress v_2966;
      v_16412 <- load v_16411 32;
      setRegister (lhs.of_reg v_2968) (concat (mux (sgt (extract v_16409 0 32) (extract v_16412 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16409 32 64) (extract v_16412 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16409 64 96) (extract v_16412 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16409 96 128) (extract v_16412 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16409 128 160) (extract v_16412 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16409 160 192) (extract v_16412 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_16409 192 224) (extract v_16412 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_16409 224 256) (extract v_16412 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
