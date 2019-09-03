def vpsignw1 : instruction :=
  definst "vpsignw" $ do
    pattern fun (v_3028 : reg (bv 128)) (v_3029 : reg (bv 128)) (v_3030 : reg (bv 128)) => do
      v_7797 <- getRegister v_3028;
      v_7798 <- eval (extract v_7797 0 16);
      v_7800 <- getRegister v_3029;
      v_7801 <- eval (extract v_7800 0 16);
      v_7809 <- eval (extract v_7797 16 32);
      v_7811 <- eval (extract v_7800 16 32);
      v_7819 <- eval (extract v_7797 32 48);
      v_7821 <- eval (extract v_7800 32 48);
      v_7829 <- eval (extract v_7797 48 64);
      v_7831 <- eval (extract v_7800 48 64);
      v_7839 <- eval (extract v_7797 64 80);
      v_7841 <- eval (extract v_7800 64 80);
      v_7849 <- eval (extract v_7797 80 96);
      v_7851 <- eval (extract v_7800 80 96);
      v_7859 <- eval (extract v_7797 96 112);
      v_7861 <- eval (extract v_7800 96 112);
      v_7869 <- eval (extract v_7797 112 128);
      v_7871 <- eval (extract v_7800 112 128);
      setRegister (lhs.of_reg v_3030) (concat (mux (sgt v_7798 (expression.bv_nat 16 0)) v_7801 (mux (eq v_7798 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7801 (mi (bitwidthMInt v_7801) -1))))) (concat (mux (sgt v_7809 (expression.bv_nat 16 0)) v_7811 (mux (eq v_7809 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7811 (mi (bitwidthMInt v_7811) -1))))) (concat (mux (sgt v_7819 (expression.bv_nat 16 0)) v_7821 (mux (eq v_7819 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7821 (mi (bitwidthMInt v_7821) -1))))) (concat (mux (sgt v_7829 (expression.bv_nat 16 0)) v_7831 (mux (eq v_7829 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7831 (mi (bitwidthMInt v_7831) -1))))) (concat (mux (sgt v_7839 (expression.bv_nat 16 0)) v_7841 (mux (eq v_7839 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7841 (mi (bitwidthMInt v_7841) -1))))) (concat (mux (sgt v_7849 (expression.bv_nat 16 0)) v_7851 (mux (eq v_7849 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7851 (mi (bitwidthMInt v_7851) -1))))) (concat (mux (sgt v_7859 (expression.bv_nat 16 0)) v_7861 (mux (eq v_7859 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7861 (mi (bitwidthMInt v_7861) -1))))) (mux (sgt v_7869 (expression.bv_nat 16 0)) v_7871 (mux (eq v_7869 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7871 (mi (bitwidthMInt v_7871) -1))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3025 : Mem) (v_3023 : reg (bv 128)) (v_3024 : reg (bv 128)) => do
      v_14822 <- evaluateAddress v_3025;
      v_14823 <- load v_14822 16;
      v_14824 <- eval (extract v_14823 0 16);
      v_14826 <- getRegister v_3023;
      v_14827 <- eval (extract v_14826 0 16);
      v_14835 <- eval (extract v_14823 16 32);
      v_14837 <- eval (extract v_14826 16 32);
      v_14845 <- eval (extract v_14823 32 48);
      v_14847 <- eval (extract v_14826 32 48);
      v_14855 <- eval (extract v_14823 48 64);
      v_14857 <- eval (extract v_14826 48 64);
      v_14865 <- eval (extract v_14823 64 80);
      v_14867 <- eval (extract v_14826 64 80);
      v_14875 <- eval (extract v_14823 80 96);
      v_14877 <- eval (extract v_14826 80 96);
      v_14885 <- eval (extract v_14823 96 112);
      v_14887 <- eval (extract v_14826 96 112);
      v_14895 <- eval (extract v_14823 112 128);
      v_14897 <- eval (extract v_14826 112 128);
      setRegister (lhs.of_reg v_3024) (concat (mux (sgt v_14824 (expression.bv_nat 16 0)) v_14827 (mux (eq v_14824 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14827 (mi (bitwidthMInt v_14827) -1))))) (concat (mux (sgt v_14835 (expression.bv_nat 16 0)) v_14837 (mux (eq v_14835 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14837 (mi (bitwidthMInt v_14837) -1))))) (concat (mux (sgt v_14845 (expression.bv_nat 16 0)) v_14847 (mux (eq v_14845 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14847 (mi (bitwidthMInt v_14847) -1))))) (concat (mux (sgt v_14855 (expression.bv_nat 16 0)) v_14857 (mux (eq v_14855 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14857 (mi (bitwidthMInt v_14857) -1))))) (concat (mux (sgt v_14865 (expression.bv_nat 16 0)) v_14867 (mux (eq v_14865 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14867 (mi (bitwidthMInt v_14867) -1))))) (concat (mux (sgt v_14875 (expression.bv_nat 16 0)) v_14877 (mux (eq v_14875 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14877 (mi (bitwidthMInt v_14877) -1))))) (concat (mux (sgt v_14885 (expression.bv_nat 16 0)) v_14887 (mux (eq v_14885 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14887 (mi (bitwidthMInt v_14887) -1))))) (mux (sgt v_14895 (expression.bv_nat 16 0)) v_14897 (mux (eq v_14895 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14897 (mi (bitwidthMInt v_14897) -1))))))))))));
      pure ()
    pat_end
