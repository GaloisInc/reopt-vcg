def psignw1 : instruction :=
  definst "psignw" $ do
    pattern fun (v_2950 : reg (bv 128)) (v_2951 : reg (bv 128)) => do
      v_7655 <- getRegister v_2950;
      v_7656 <- eval (extract v_7655 0 16);
      v_7658 <- getRegister v_2951;
      v_7659 <- eval (extract v_7658 0 16);
      v_7667 <- eval (extract v_7655 16 32);
      v_7669 <- eval (extract v_7658 16 32);
      v_7677 <- eval (extract v_7655 32 48);
      v_7679 <- eval (extract v_7658 32 48);
      v_7687 <- eval (extract v_7655 48 64);
      v_7689 <- eval (extract v_7658 48 64);
      v_7697 <- eval (extract v_7655 64 80);
      v_7699 <- eval (extract v_7658 64 80);
      v_7707 <- eval (extract v_7655 80 96);
      v_7709 <- eval (extract v_7658 80 96);
      v_7717 <- eval (extract v_7655 96 112);
      v_7719 <- eval (extract v_7658 96 112);
      v_7727 <- eval (extract v_7655 112 128);
      v_7729 <- eval (extract v_7658 112 128);
      setRegister (lhs.of_reg v_2951) (concat (mux (sgt v_7656 (expression.bv_nat 16 0)) v_7659 (mux (eq v_7656 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7659 (mi (bitwidthMInt v_7659) -1))))) (concat (mux (sgt v_7667 (expression.bv_nat 16 0)) v_7669 (mux (eq v_7667 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7669 (mi (bitwidthMInt v_7669) -1))))) (concat (mux (sgt v_7677 (expression.bv_nat 16 0)) v_7679 (mux (eq v_7677 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7679 (mi (bitwidthMInt v_7679) -1))))) (concat (mux (sgt v_7687 (expression.bv_nat 16 0)) v_7689 (mux (eq v_7687 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7689 (mi (bitwidthMInt v_7689) -1))))) (concat (mux (sgt v_7697 (expression.bv_nat 16 0)) v_7699 (mux (eq v_7697 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7699 (mi (bitwidthMInt v_7699) -1))))) (concat (mux (sgt v_7707 (expression.bv_nat 16 0)) v_7709 (mux (eq v_7707 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7709 (mi (bitwidthMInt v_7709) -1))))) (concat (mux (sgt v_7717 (expression.bv_nat 16 0)) v_7719 (mux (eq v_7717 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7719 (mi (bitwidthMInt v_7719) -1))))) (mux (sgt v_7727 (expression.bv_nat 16 0)) v_7729 (mux (eq v_7727 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7729 (mi (bitwidthMInt v_7729) -1))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2945 : Mem) (v_2946 : reg (bv 128)) => do
      v_14861 <- evaluateAddress v_2945;
      v_14862 <- load v_14861 16;
      v_14863 <- eval (extract v_14862 0 16);
      v_14865 <- getRegister v_2946;
      v_14866 <- eval (extract v_14865 0 16);
      v_14874 <- eval (extract v_14862 16 32);
      v_14876 <- eval (extract v_14865 16 32);
      v_14884 <- eval (extract v_14862 32 48);
      v_14886 <- eval (extract v_14865 32 48);
      v_14894 <- eval (extract v_14862 48 64);
      v_14896 <- eval (extract v_14865 48 64);
      v_14904 <- eval (extract v_14862 64 80);
      v_14906 <- eval (extract v_14865 64 80);
      v_14914 <- eval (extract v_14862 80 96);
      v_14916 <- eval (extract v_14865 80 96);
      v_14924 <- eval (extract v_14862 96 112);
      v_14926 <- eval (extract v_14865 96 112);
      v_14934 <- eval (extract v_14862 112 128);
      v_14936 <- eval (extract v_14865 112 128);
      setRegister (lhs.of_reg v_2946) (concat (mux (sgt v_14863 (expression.bv_nat 16 0)) v_14866 (mux (eq v_14863 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14866 (mi (bitwidthMInt v_14866) -1))))) (concat (mux (sgt v_14874 (expression.bv_nat 16 0)) v_14876 (mux (eq v_14874 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14876 (mi (bitwidthMInt v_14876) -1))))) (concat (mux (sgt v_14884 (expression.bv_nat 16 0)) v_14886 (mux (eq v_14884 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14886 (mi (bitwidthMInt v_14886) -1))))) (concat (mux (sgt v_14894 (expression.bv_nat 16 0)) v_14896 (mux (eq v_14894 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14896 (mi (bitwidthMInt v_14896) -1))))) (concat (mux (sgt v_14904 (expression.bv_nat 16 0)) v_14906 (mux (eq v_14904 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14906 (mi (bitwidthMInt v_14906) -1))))) (concat (mux (sgt v_14914 (expression.bv_nat 16 0)) v_14916 (mux (eq v_14914 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14916 (mi (bitwidthMInt v_14916) -1))))) (concat (mux (sgt v_14924 (expression.bv_nat 16 0)) v_14926 (mux (eq v_14924 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14926 (mi (bitwidthMInt v_14926) -1))))) (mux (sgt v_14934 (expression.bv_nat 16 0)) v_14936 (mux (eq v_14934 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14936 (mi (bitwidthMInt v_14936) -1))))))))))));
      pure ()
    pat_end
