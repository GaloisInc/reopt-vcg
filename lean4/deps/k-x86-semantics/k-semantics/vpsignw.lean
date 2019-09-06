def vpsignw1 : instruction :=
  definst "vpsignw" $ do
    pattern fun (v_3120 : reg (bv 128)) (v_3121 : reg (bv 128)) (v_3122 : reg (bv 128)) => do
      v_7602 <- getRegister v_3120;
      v_7603 <- eval (extract v_7602 0 16);
      v_7605 <- getRegister v_3121;
      v_7606 <- eval (extract v_7605 0 16);
      v_7612 <- eval (extract v_7602 16 32);
      v_7614 <- eval (extract v_7605 16 32);
      v_7620 <- eval (extract v_7602 32 48);
      v_7622 <- eval (extract v_7605 32 48);
      v_7628 <- eval (extract v_7602 48 64);
      v_7630 <- eval (extract v_7605 48 64);
      v_7636 <- eval (extract v_7602 64 80);
      v_7638 <- eval (extract v_7605 64 80);
      v_7644 <- eval (extract v_7602 80 96);
      v_7646 <- eval (extract v_7605 80 96);
      v_7652 <- eval (extract v_7602 96 112);
      v_7654 <- eval (extract v_7605 96 112);
      v_7660 <- eval (extract v_7602 112 128);
      v_7662 <- eval (extract v_7605 112 128);
      setRegister (lhs.of_reg v_3122) (concat (mux (sgt v_7603 (expression.bv_nat 16 0)) v_7606 (mux (eq v_7603 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7606 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7612 (expression.bv_nat 16 0)) v_7614 (mux (eq v_7612 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7614 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7620 (expression.bv_nat 16 0)) v_7622 (mux (eq v_7620 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7622 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7628 (expression.bv_nat 16 0)) v_7630 (mux (eq v_7628 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7630 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7636 (expression.bv_nat 16 0)) v_7638 (mux (eq v_7636 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7638 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7644 (expression.bv_nat 16 0)) v_7646 (mux (eq v_7644 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7646 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7652 (expression.bv_nat 16 0)) v_7654 (mux (eq v_7652 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7654 (expression.bv_nat 16 65535))))) (mux (sgt v_7660 (expression.bv_nat 16 0)) v_7662 (mux (eq v_7660 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7662 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3114 : Mem) (v_3115 : reg (bv 128)) (v_3116 : reg (bv 128)) => do
      v_13880 <- evaluateAddress v_3114;
      v_13881 <- load v_13880 16;
      v_13882 <- eval (extract v_13881 0 16);
      v_13884 <- getRegister v_3115;
      v_13885 <- eval (extract v_13884 0 16);
      v_13891 <- eval (extract v_13881 16 32);
      v_13893 <- eval (extract v_13884 16 32);
      v_13899 <- eval (extract v_13881 32 48);
      v_13901 <- eval (extract v_13884 32 48);
      v_13907 <- eval (extract v_13881 48 64);
      v_13909 <- eval (extract v_13884 48 64);
      v_13915 <- eval (extract v_13881 64 80);
      v_13917 <- eval (extract v_13884 64 80);
      v_13923 <- eval (extract v_13881 80 96);
      v_13925 <- eval (extract v_13884 80 96);
      v_13931 <- eval (extract v_13881 96 112);
      v_13933 <- eval (extract v_13884 96 112);
      v_13939 <- eval (extract v_13881 112 128);
      v_13941 <- eval (extract v_13884 112 128);
      setRegister (lhs.of_reg v_3116) (concat (mux (sgt v_13882 (expression.bv_nat 16 0)) v_13885 (mux (eq v_13882 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13885 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13891 (expression.bv_nat 16 0)) v_13893 (mux (eq v_13891 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13893 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13899 (expression.bv_nat 16 0)) v_13901 (mux (eq v_13899 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13901 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13907 (expression.bv_nat 16 0)) v_13909 (mux (eq v_13907 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13909 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13915 (expression.bv_nat 16 0)) v_13917 (mux (eq v_13915 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13917 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13923 (expression.bv_nat 16 0)) v_13925 (mux (eq v_13923 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13925 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13931 (expression.bv_nat 16 0)) v_13933 (mux (eq v_13931 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13933 (expression.bv_nat 16 65535))))) (mux (sgt v_13939 (expression.bv_nat 16 0)) v_13941 (mux (eq v_13939 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13941 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end
