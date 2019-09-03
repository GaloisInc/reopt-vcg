def vminpd1 : instruction :=
  definst "vminpd" $ do
    pattern fun (v_2617 : reg (bv 128)) (v_2618 : reg (bv 128)) (v_2619 : reg (bv 128)) => do
      v_4857 <- getRegister v_2618;
      v_4858 <- eval (extract v_4857 0 64);
      v_4859 <- getRegister v_2617;
      v_4860 <- eval (extract v_4859 0 64);
      v_4864 <- eval (extract v_4857 64 128);
      v_4865 <- eval (extract v_4859 64 128);
      setRegister (lhs.of_reg v_2619) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4858 v_4860) (expression.bv_nat 1 1)) v_4858 v_4860) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4864 v_4865) (expression.bv_nat 1 1)) v_4864 v_4865));
      pure ()
    pat_end;
    pattern fun (v_2628 : reg (bv 256)) (v_2629 : reg (bv 256)) (v_2630 : reg (bv 256)) => do
      v_4876 <- getRegister v_2629;
      v_4877 <- eval (extract v_4876 0 64);
      v_4878 <- getRegister v_2628;
      v_4879 <- eval (extract v_4878 0 64);
      v_4883 <- eval (extract v_4876 64 128);
      v_4884 <- eval (extract v_4878 64 128);
      v_4888 <- eval (extract v_4876 128 192);
      v_4889 <- eval (extract v_4878 128 192);
      v_4893 <- eval (extract v_4876 192 256);
      v_4894 <- eval (extract v_4878 192 256);
      setRegister (lhs.of_reg v_2630) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4877 v_4879) (expression.bv_nat 1 1)) v_4877 v_4879) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4883 v_4884) (expression.bv_nat 1 1)) v_4883 v_4884) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4888 v_4889) (expression.bv_nat 1 1)) v_4888 v_4889) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4893 v_4894) (expression.bv_nat 1 1)) v_4893 v_4894))));
      pure ()
    pat_end;
    pattern fun (v_2612 : Mem) (v_2613 : reg (bv 128)) (v_2614 : reg (bv 128)) => do
      v_10923 <- getRegister v_2613;
      v_10924 <- eval (extract v_10923 0 64);
      v_10925 <- evaluateAddress v_2612;
      v_10926 <- load v_10925 16;
      v_10927 <- eval (extract v_10926 0 64);
      v_10931 <- eval (extract v_10923 64 128);
      v_10932 <- eval (extract v_10926 64 128);
      setRegister (lhs.of_reg v_2614) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10924 v_10927) (expression.bv_nat 1 1)) v_10924 v_10927) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10931 v_10932) (expression.bv_nat 1 1)) v_10931 v_10932));
      pure ()
    pat_end;
    pattern fun (v_2623 : Mem) (v_2624 : reg (bv 256)) (v_2625 : reg (bv 256)) => do
      v_10938 <- getRegister v_2624;
      v_10939 <- eval (extract v_10938 0 64);
      v_10940 <- evaluateAddress v_2623;
      v_10941 <- load v_10940 32;
      v_10942 <- eval (extract v_10941 0 64);
      v_10946 <- eval (extract v_10938 64 128);
      v_10947 <- eval (extract v_10941 64 128);
      v_10951 <- eval (extract v_10938 128 192);
      v_10952 <- eval (extract v_10941 128 192);
      v_10956 <- eval (extract v_10938 192 256);
      v_10957 <- eval (extract v_10941 192 256);
      setRegister (lhs.of_reg v_2625) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10939 v_10942) (expression.bv_nat 1 1)) v_10939 v_10942) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10946 v_10947) (expression.bv_nat 1 1)) v_10946 v_10947) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10951 v_10952) (expression.bv_nat 1 1)) v_10951 v_10952) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10956 v_10957) (expression.bv_nat 1 1)) v_10956 v_10957))));
      pure ()
    pat_end
