def vpsignd1 : instruction :=
  definst "vpsignd" $ do
    pattern fun (v_3082 : reg (bv 128)) (v_3083 : reg (bv 128)) (v_3084 : reg (bv 128)) => do
      v_7532 <- getRegister v_3082;
      v_7533 <- eval (extract v_7532 0 32);
      v_7535 <- getRegister v_3083;
      v_7536 <- eval (extract v_7535 0 32);
      v_7542 <- eval (extract v_7532 32 64);
      v_7544 <- eval (extract v_7535 32 64);
      v_7550 <- eval (extract v_7532 64 96);
      v_7552 <- eval (extract v_7535 64 96);
      v_7558 <- eval (extract v_7532 96 128);
      v_7560 <- eval (extract v_7535 96 128);
      setRegister (lhs.of_reg v_3084) (concat (mux (sgt v_7533 (expression.bv_nat 32 0)) v_7536 (mux (eq v_7533 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7536 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7542 (expression.bv_nat 32 0)) v_7544 (mux (eq v_7542 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7544 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_7550 (expression.bv_nat 32 0)) v_7552 (mux (eq v_7550 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7552 (expression.bv_nat 32 4294967295))))) (mux (sgt v_7558 (expression.bv_nat 32 0)) v_7560 (mux (eq v_7558 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7560 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end;
    pattern fun (v_3076 : Mem) (v_3077 : reg (bv 128)) (v_3078 : reg (bv 128)) => do
      v_13814 <- evaluateAddress v_3076;
      v_13815 <- load v_13814 16;
      v_13816 <- eval (extract v_13815 0 32);
      v_13818 <- getRegister v_3077;
      v_13819 <- eval (extract v_13818 0 32);
      v_13825 <- eval (extract v_13815 32 64);
      v_13827 <- eval (extract v_13818 32 64);
      v_13833 <- eval (extract v_13815 64 96);
      v_13835 <- eval (extract v_13818 64 96);
      v_13841 <- eval (extract v_13815 96 128);
      v_13843 <- eval (extract v_13818 96 128);
      setRegister (lhs.of_reg v_3078) (concat (mux (sgt v_13816 (expression.bv_nat 32 0)) v_13819 (mux (eq v_13816 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13819 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_13825 (expression.bv_nat 32 0)) v_13827 (mux (eq v_13825 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13827 (expression.bv_nat 32 4294967295))))) (concat (mux (sgt v_13833 (expression.bv_nat 32 0)) v_13835 (mux (eq v_13833 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13835 (expression.bv_nat 32 4294967295))))) (mux (sgt v_13841 (expression.bv_nat 32 0)) v_13843 (mux (eq v_13841 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_13843 (expression.bv_nat 32 4294967295))))))));
      pure ()
    pat_end
