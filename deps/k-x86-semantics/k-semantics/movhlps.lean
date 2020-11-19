def movhlps : instruction :=
  definst "movhlps" $ do
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      setRegister (lhs.of_reg xmm_1) (concat v_3 v_5);
      pure ()
    pat_end
