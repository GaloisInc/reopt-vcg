def vblendvpd1 : instruction :=
  definst "vblendvpd" $ do
    pattern fun (v_2834 : reg (bv 128)) (v_2835 : reg (bv 128)) (v_2836 : reg (bv 128)) (v_2837 : reg (bv 128)) => do
      v_5841 <- getRegister v_2834;
      v_5844 <- getRegister v_2836;
      v_5846 <- getRegister v_2835;
      setRegister (lhs.of_reg v_2837) (concat (mux (eq (extract v_5841 0 1) (expression.bv_nat 1 0)) (extract v_5844 0 64) (extract v_5846 0 64)) (mux (eq (extract v_5841 64 65) (expression.bv_nat 1 0)) (extract v_5844 64 128) (extract v_5846 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2844 : reg (bv 256)) (v_2845 : reg (bv 256)) (v_2846 : reg (bv 256)) (v_2847 : reg (bv 256)) => do
      v_5862 <- getRegister v_2844;
      v_5865 <- getRegister v_2846;
      v_5867 <- getRegister v_2845;
      setRegister (lhs.of_reg v_2847) (concat (mux (eq (extract v_5862 0 1) (expression.bv_nat 1 0)) (extract v_5865 0 64) (extract v_5867 0 64)) (concat (mux (eq (extract v_5862 64 65) (expression.bv_nat 1 0)) (extract v_5865 64 128) (extract v_5867 64 128)) (concat (mux (eq (extract v_5862 128 129) (expression.bv_nat 1 0)) (extract v_5865 128 192) (extract v_5867 128 192)) (mux (eq (extract v_5862 192 193) (expression.bv_nat 1 0)) (extract v_5865 192 256) (extract v_5867 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2828 : reg (bv 128)) (v_2825 : Mem) (v_2829 : reg (bv 128)) (v_2830 : reg (bv 128)) => do
      v_11298 <- getRegister v_2828;
      v_11301 <- getRegister v_2829;
      v_11303 <- evaluateAddress v_2825;
      v_11304 <- load v_11303 16;
      setRegister (lhs.of_reg v_2830) (concat (mux (eq (extract v_11298 0 1) (expression.bv_nat 1 0)) (extract v_11301 0 64) (extract v_11304 0 64)) (mux (eq (extract v_11298 64 65) (expression.bv_nat 1 0)) (extract v_11301 64 128) (extract v_11304 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2839 : reg (bv 256)) (v_2838 : Mem) (v_2840 : reg (bv 256)) (v_2841 : reg (bv 256)) => do
      v_11314 <- getRegister v_2839;
      v_11317 <- getRegister v_2840;
      v_11319 <- evaluateAddress v_2838;
      v_11320 <- load v_11319 32;
      setRegister (lhs.of_reg v_2841) (concat (mux (eq (extract v_11314 0 1) (expression.bv_nat 1 0)) (extract v_11317 0 64) (extract v_11320 0 64)) (concat (mux (eq (extract v_11314 64 65) (expression.bv_nat 1 0)) (extract v_11317 64 128) (extract v_11320 64 128)) (concat (mux (eq (extract v_11314 128 129) (expression.bv_nat 1 0)) (extract v_11317 128 192) (extract v_11320 128 192)) (mux (eq (extract v_11314 192 193) (expression.bv_nat 1 0)) (extract v_11317 192 256) (extract v_11320 192 256)))));
      pure ()
    pat_end
