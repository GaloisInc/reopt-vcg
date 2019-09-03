def vpcmpeqd1 : instruction :=
  definst "vpcmpeqd" $ do
    pattern fun (v_2782 : reg (bv 128)) (v_2783 : reg (bv 128)) (v_2784 : reg (bv 128)) => do
      v_7513 <- getRegister v_2783;
      v_7515 <- getRegister v_2782;
      setRegister (lhs.of_reg v_2784) (concat (mux (eq (extract v_7513 0 32) (extract v_7515 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7513 32 64) (extract v_7515 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7513 64 96) (extract v_7515 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7513 96 128) (extract v_7515 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2793 : reg (bv 256)) (v_2794 : reg (bv 256)) (v_2795 : reg (bv 256)) => do
      v_7540 <- getRegister v_2794;
      v_7542 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2795) (concat (mux (eq (extract v_7540 0 32) (extract v_7542 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7540 32 64) (extract v_7542 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7540 64 96) (extract v_7542 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7540 96 128) (extract v_7542 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7540 128 160) (extract v_7542 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7540 160 192) (extract v_7542 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7540 192 224) (extract v_7542 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7540 224 256) (extract v_7542 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2776 : Mem) (v_2777 : reg (bv 128)) (v_2778 : reg (bv 128)) => do
      v_16741 <- getRegister v_2777;
      v_16743 <- evaluateAddress v_2776;
      v_16744 <- load v_16743 16;
      setRegister (lhs.of_reg v_2778) (concat (mux (eq (extract v_16741 0 32) (extract v_16744 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16741 32 64) (extract v_16744 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16741 64 96) (extract v_16744 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_16741 96 128) (extract v_16744 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2787 : Mem) (v_2788 : reg (bv 256)) (v_2789 : reg (bv 256)) => do
      v_16764 <- getRegister v_2788;
      v_16766 <- evaluateAddress v_2787;
      v_16767 <- load v_16766 32;
      setRegister (lhs.of_reg v_2789) (concat (mux (eq (extract v_16764 0 32) (extract v_16767 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16764 32 64) (extract v_16767 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16764 64 96) (extract v_16767 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16764 96 128) (extract v_16767 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16764 128 160) (extract v_16767 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16764 160 192) (extract v_16767 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_16764 192 224) (extract v_16767 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_16764 224 256) (extract v_16767 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
