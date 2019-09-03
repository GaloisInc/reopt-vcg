def psignd1 : instruction :=
  definst "psignd" $ do
    pattern fun (v_2941 : reg (bv 128)) (v_2942 : reg (bv 128)) => do
      v_7605 <- getRegister v_2941;
      v_7606 <- eval (extract v_7605 0 32);
      v_7608 <- getRegister v_2942;
      v_7609 <- eval (extract v_7608 0 32);
      v_7617 <- eval (extract v_7605 32 64);
      v_7619 <- eval (extract v_7608 32 64);
      v_7627 <- eval (extract v_7605 64 96);
      v_7629 <- eval (extract v_7608 64 96);
      v_7637 <- eval (extract v_7605 96 128);
      v_7639 <- eval (extract v_7608 96 128);
      setRegister (lhs.of_reg v_2942) (concat (mux (sgt v_7606 (expression.bv_nat 32 0)) v_7609 (mux (eq v_7606 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7609 (mi (bitwidthMInt v_7609) -1))))) (concat (mux (sgt v_7617 (expression.bv_nat 32 0)) v_7619 (mux (eq v_7617 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7619 (mi (bitwidthMInt v_7619) -1))))) (concat (mux (sgt v_7627 (expression.bv_nat 32 0)) v_7629 (mux (eq v_7627 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7629 (mi (bitwidthMInt v_7629) -1))))) (mux (sgt v_7637 (expression.bv_nat 32 0)) v_7639 (mux (eq v_7637 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7639 (mi (bitwidthMInt v_7639) -1))))))));
      pure ()
    pat_end;
    pattern fun (v_2936 : Mem) (v_2937 : reg (bv 128)) => do
      v_14814 <- evaluateAddress v_2936;
      v_14815 <- load v_14814 16;
      v_14816 <- eval (extract v_14815 0 32);
      v_14818 <- getRegister v_2937;
      v_14819 <- eval (extract v_14818 0 32);
      v_14827 <- eval (extract v_14815 32 64);
      v_14829 <- eval (extract v_14818 32 64);
      v_14837 <- eval (extract v_14815 64 96);
      v_14839 <- eval (extract v_14818 64 96);
      v_14847 <- eval (extract v_14815 96 128);
      v_14849 <- eval (extract v_14818 96 128);
      setRegister (lhs.of_reg v_2937) (concat (mux (sgt v_14816 (expression.bv_nat 32 0)) v_14819 (mux (eq v_14816 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14819 (mi (bitwidthMInt v_14819) -1))))) (concat (mux (sgt v_14827 (expression.bv_nat 32 0)) v_14829 (mux (eq v_14827 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14829 (mi (bitwidthMInt v_14829) -1))))) (concat (mux (sgt v_14837 (expression.bv_nat 32 0)) v_14839 (mux (eq v_14837 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14839 (mi (bitwidthMInt v_14839) -1))))) (mux (sgt v_14847 (expression.bv_nat 32 0)) v_14849 (mux (eq v_14847 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14849 (mi (bitwidthMInt v_14849) -1))))))));
      pure ()
    pat_end
