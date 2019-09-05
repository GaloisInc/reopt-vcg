def vpsignw1 : instruction :=
  definst "vpsignw" $ do
    pattern fun (v_3093 : reg (bv 128)) (v_3094 : reg (bv 128)) (v_3095 : reg (bv 128)) => do
      v_7575 <- getRegister v_3093;
      v_7576 <- eval (extract v_7575 0 16);
      v_7578 <- getRegister v_3094;
      v_7579 <- eval (extract v_7578 0 16);
      v_7585 <- eval (extract v_7575 16 32);
      v_7587 <- eval (extract v_7578 16 32);
      v_7593 <- eval (extract v_7575 32 48);
      v_7595 <- eval (extract v_7578 32 48);
      v_7601 <- eval (extract v_7575 48 64);
      v_7603 <- eval (extract v_7578 48 64);
      v_7609 <- eval (extract v_7575 64 80);
      v_7611 <- eval (extract v_7578 64 80);
      v_7617 <- eval (extract v_7575 80 96);
      v_7619 <- eval (extract v_7578 80 96);
      v_7625 <- eval (extract v_7575 96 112);
      v_7627 <- eval (extract v_7578 96 112);
      v_7633 <- eval (extract v_7575 112 128);
      v_7635 <- eval (extract v_7578 112 128);
      setRegister (lhs.of_reg v_3095) (concat (mux (sgt v_7576 (expression.bv_nat 16 0)) v_7579 (mux (eq v_7576 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7579 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7585 (expression.bv_nat 16 0)) v_7587 (mux (eq v_7585 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7587 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7593 (expression.bv_nat 16 0)) v_7595 (mux (eq v_7593 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7595 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7601 (expression.bv_nat 16 0)) v_7603 (mux (eq v_7601 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7603 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7609 (expression.bv_nat 16 0)) v_7611 (mux (eq v_7609 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7611 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7617 (expression.bv_nat 16 0)) v_7619 (mux (eq v_7617 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7619 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7625 (expression.bv_nat 16 0)) v_7627 (mux (eq v_7625 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7627 (expression.bv_nat 16 65535))))) (mux (sgt v_7633 (expression.bv_nat 16 0)) v_7635 (mux (eq v_7633 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7635 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3087 : Mem) (v_3088 : reg (bv 128)) (v_3089 : reg (bv 128)) => do
      v_13853 <- evaluateAddress v_3087;
      v_13854 <- load v_13853 16;
      v_13855 <- eval (extract v_13854 0 16);
      v_13857 <- getRegister v_3088;
      v_13858 <- eval (extract v_13857 0 16);
      v_13864 <- eval (extract v_13854 16 32);
      v_13866 <- eval (extract v_13857 16 32);
      v_13872 <- eval (extract v_13854 32 48);
      v_13874 <- eval (extract v_13857 32 48);
      v_13880 <- eval (extract v_13854 48 64);
      v_13882 <- eval (extract v_13857 48 64);
      v_13888 <- eval (extract v_13854 64 80);
      v_13890 <- eval (extract v_13857 64 80);
      v_13896 <- eval (extract v_13854 80 96);
      v_13898 <- eval (extract v_13857 80 96);
      v_13904 <- eval (extract v_13854 96 112);
      v_13906 <- eval (extract v_13857 96 112);
      v_13912 <- eval (extract v_13854 112 128);
      v_13914 <- eval (extract v_13857 112 128);
      setRegister (lhs.of_reg v_3089) (concat (mux (sgt v_13855 (expression.bv_nat 16 0)) v_13858 (mux (eq v_13855 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13858 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13864 (expression.bv_nat 16 0)) v_13866 (mux (eq v_13864 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13866 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13872 (expression.bv_nat 16 0)) v_13874 (mux (eq v_13872 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13874 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13880 (expression.bv_nat 16 0)) v_13882 (mux (eq v_13880 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13882 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13888 (expression.bv_nat 16 0)) v_13890 (mux (eq v_13888 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13890 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13896 (expression.bv_nat 16 0)) v_13898 (mux (eq v_13896 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13898 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13904 (expression.bv_nat 16 0)) v_13906 (mux (eq v_13904 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13906 (expression.bv_nat 16 65535))))) (mux (sgt v_13912 (expression.bv_nat 16 0)) v_13914 (mux (eq v_13912 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13914 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end
