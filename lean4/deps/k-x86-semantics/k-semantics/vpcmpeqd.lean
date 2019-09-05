def vpcmpeqd1 : instruction :=
  definst "vpcmpeqd" $ do
    pattern fun (v_2846 : reg (bv 128)) (v_2847 : reg (bv 128)) (v_2848 : reg (bv 128)) => do
      v_7277 <- getRegister v_2847;
      v_7279 <- getRegister v_2846;
      setRegister (lhs.of_reg v_2848) (concat (mux (eq (extract v_7277 0 32) (extract v_7279 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7277 32 64) (extract v_7279 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7277 64 96) (extract v_7279 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7277 96 128) (extract v_7279 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2856 : reg (bv 256)) (v_2857 : reg (bv 256)) (v_2858 : reg (bv 256)) => do
      v_7304 <- getRegister v_2857;
      v_7306 <- getRegister v_2856;
      setRegister (lhs.of_reg v_2858) (concat (mux (eq (extract v_7304 0 32) (extract v_7306 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 32 64) (extract v_7306 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 64 96) (extract v_7306 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 96 128) (extract v_7306 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 128 160) (extract v_7306 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 160 192) (extract v_7306 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_7304 192 224) (extract v_7306 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_7304 224 256) (extract v_7306 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2840 : Mem) (v_2841 : reg (bv 128)) (v_2842 : reg (bv 128)) => do
      v_15885 <- getRegister v_2841;
      v_15887 <- evaluateAddress v_2840;
      v_15888 <- load v_15887 16;
      setRegister (lhs.of_reg v_2842) (concat (mux (eq (extract v_15885 0 32) (extract v_15888 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15885 32 64) (extract v_15888 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15885 64 96) (extract v_15888 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_15885 96 128) (extract v_15888 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2851 : Mem) (v_2852 : reg (bv 256)) (v_2853 : reg (bv 256)) => do
      v_15908 <- getRegister v_2852;
      v_15910 <- evaluateAddress v_2851;
      v_15911 <- load v_15910 32;
      setRegister (lhs.of_reg v_2853) (concat (mux (eq (extract v_15908 0 32) (extract v_15911 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15908 32 64) (extract v_15911 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15908 64 96) (extract v_15911 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15908 96 128) (extract v_15911 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15908 128 160) (extract v_15911 128 160)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15908 160 192) (extract v_15911 160 192)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_15908 192 224) (extract v_15911 192 224)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_15908 224 256) (extract v_15911 224 256)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end
