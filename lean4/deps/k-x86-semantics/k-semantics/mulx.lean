def mulx1 : instruction :=
  definst "mulx" $ do
    pattern fun (v_2872 : reg (bv 32)) (v_2873 : reg (bv 32)) (v_2874 : reg (bv 32)) => do
      v_7082 <- getRegister rdx;
      v_7085 <- getRegister v_2872;
      v_7087 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_7082 32 64)) (concat (expression.bv_nat 32 0) v_7085));
      setRegister (lhs.of_reg v_2874) (extract v_7087 0 32);
      setRegister (lhs.of_reg v_2873) (extract v_7087 32 64);
      pure ()
    pat_end;
    pattern fun (v_2893 : reg (bv 64)) (v_2894 : reg (bv 64)) (v_2895 : reg (bv 64)) => do
      v_7103 <- getRegister rdx;
      v_7105 <- getRegister v_2893;
      v_7107 <- eval (mul (concat (expression.bv_nat 64 0) v_7103) (concat (expression.bv_nat 64 0) v_7105));
      setRegister (lhs.of_reg v_2894) (extract v_7107 64 128);
      setRegister (lhs.of_reg v_2895) (extract v_7107 0 64);
      pure ()
    pat_end;
    pattern fun (v_2862 : Mem) (v_2863 : reg (bv 32)) (v_2864 : reg (bv 32)) => do
      v_10701 <- evaluateAddress v_2862;
      v_10704 <- load v_10701 4;
      v_10706 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_10701 32 64)) (concat (expression.bv_nat 32 0) v_10704));
      setRegister (lhs.of_reg v_2864) (extract v_10706 0 32);
      setRegister (lhs.of_reg v_2863) (extract v_10706 32 64);
      pure ()
    pat_end;
    pattern fun (v_2883 : Mem) (v_2884 : reg (bv 64)) (v_2885 : reg (bv 64)) => do
      v_10711 <- evaluateAddress v_2883;
      v_10713 <- load v_10711 8;
      v_10715 <- eval (mul (concat (expression.bv_nat 64 0) v_10711) (concat (expression.bv_nat 64 0) v_10713));
      setRegister (lhs.of_reg v_2885) (extract v_10715 0 64);
      setRegister (lhs.of_reg v_2884) (extract v_10715 64 128);
      pure ()
    pat_end
