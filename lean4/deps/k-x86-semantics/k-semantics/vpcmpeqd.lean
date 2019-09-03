def vpcmpeqd1 : instruction :=
  definst "vpcmpeqd" $ do
    pattern fun (v_2792 : reg (bv 128)) (v_2793 : reg (bv 128)) (v_2794 : reg (bv 128)) => do
      v_7376 <- getRegister v_2793;
      v_7378 <- getRegister v_2792;
      setRegister (lhs.of_reg v_2794) (concat (mux (eq (extract v_7376 0 32) (extract v_7378 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7376 32 64) (extract v_7378 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7376 64 96) (extract v_7378 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7376 96 128) (extract v_7378 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2806 : reg (bv 256)) (v_2807 : reg (bv 256)) (v_2808 : reg (bv 256)) => do
      v_7403 <- getRegister v_2807;
      v_7405 <- getRegister v_2806;
      setRegister (lhs.of_reg v_2808) (concat (mux (eq (extract v_7403 0 32) (extract v_7405 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7403 32 64) (extract v_7405 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7403 64 96) (extract v_7405 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7403 96 128) (extract v_7405 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7403 128 160) (extract v_7405 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7403 160 192) (extract v_7405 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7403 192 224) (extract v_7405 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7403 224 256) (extract v_7405 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2791 : Mem) (v_2787 : reg (bv 128)) (v_2788 : reg (bv 128)) => do
      v_16232 <- getRegister v_2787;
      v_16234 <- evaluateAddress v_2791;
      v_16235 <- load v_16234 16;
      setRegister (lhs.of_reg v_2788) (concat (mux (eq (extract v_16232 0 32) (extract v_16235 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16232 32 64) (extract v_16235 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16232 64 96) (extract v_16235 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_16232 96 128) (extract v_16235 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2800 : Mem) (v_2801 : reg (bv 256)) (v_2802 : reg (bv 256)) => do
      v_16255 <- getRegister v_2801;
      v_16257 <- evaluateAddress v_2800;
      v_16258 <- load v_16257 32;
      setRegister (lhs.of_reg v_2802) (concat (mux (eq (extract v_16255 0 32) (extract v_16258 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16255 32 64) (extract v_16258 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16255 64 96) (extract v_16258 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16255 96 128) (extract v_16258 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16255 128 160) (extract v_16258 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16255 160 192) (extract v_16258 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16255 192 224) (extract v_16258 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_16255 224 256) (extract v_16258 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
