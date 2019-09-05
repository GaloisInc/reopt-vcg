def vmaxps1 : instruction :=
  definst "vmaxps" $ do
    pattern fun (v_2624 : reg (bv 128)) (v_2625 : reg (bv 128)) (v_2626 : reg (bv 128)) => do
      v_4426 <- getRegister v_2625;
      v_4427 <- eval (extract v_4426 0 32);
      v_4428 <- getRegister v_2624;
      v_4429 <- eval (extract v_4428 0 32);
      v_4433 <- eval (extract v_4426 32 64);
      v_4434 <- eval (extract v_4428 32 64);
      v_4438 <- eval (extract v_4426 64 96);
      v_4439 <- eval (extract v_4428 64 96);
      v_4443 <- eval (extract v_4426 96 128);
      v_4444 <- eval (extract v_4428 96 128);
      setRegister (lhs.of_reg v_2626) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4427 v_4429) (expression.bv_nat 1 1)) v_4427 v_4429) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4433 v_4434) (expression.bv_nat 1 1)) v_4433 v_4434) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4438 v_4439) (expression.bv_nat 1 1)) v_4438 v_4439) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4443 v_4444) (expression.bv_nat 1 1)) v_4443 v_4444))));
      pure ()
    pat_end;
    pattern fun (v_2636 : reg (bv 256)) (v_2637 : reg (bv 256)) (v_2638 : reg (bv 256)) => do
      v_4457 <- getRegister v_2637;
      v_4458 <- eval (extract v_4457 0 32);
      v_4459 <- getRegister v_2636;
      v_4460 <- eval (extract v_4459 0 32);
      v_4464 <- eval (extract v_4457 32 64);
      v_4465 <- eval (extract v_4459 32 64);
      v_4469 <- eval (extract v_4457 64 96);
      v_4470 <- eval (extract v_4459 64 96);
      v_4474 <- eval (extract v_4457 96 128);
      v_4475 <- eval (extract v_4459 96 128);
      v_4479 <- eval (extract v_4457 128 160);
      v_4480 <- eval (extract v_4459 128 160);
      v_4484 <- eval (extract v_4457 160 192);
      v_4485 <- eval (extract v_4459 160 192);
      v_4489 <- eval (extract v_4457 192 224);
      v_4490 <- eval (extract v_4459 192 224);
      v_4494 <- eval (extract v_4457 224 256);
      v_4495 <- eval (extract v_4459 224 256);
      setRegister (lhs.of_reg v_2638) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4458 v_4460) (expression.bv_nat 1 1)) v_4458 v_4460) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4464 v_4465) (expression.bv_nat 1 1)) v_4464 v_4465) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4469 v_4470) (expression.bv_nat 1 1)) v_4469 v_4470) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4474 v_4475) (expression.bv_nat 1 1)) v_4474 v_4475) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4479 v_4480) (expression.bv_nat 1 1)) v_4479 v_4480) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4484 v_4485) (expression.bv_nat 1 1)) v_4484 v_4485) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4489 v_4490) (expression.bv_nat 1 1)) v_4489 v_4490) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4494 v_4495) (expression.bv_nat 1 1)) v_4494 v_4495))))))));
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) (v_2620 : reg (bv 128)) (v_2621 : reg (bv 128)) => do
      v_9886 <- getRegister v_2620;
      v_9887 <- eval (extract v_9886 0 32);
      v_9888 <- evaluateAddress v_2619;
      v_9889 <- load v_9888 16;
      v_9890 <- eval (extract v_9889 0 32);
      v_9894 <- eval (extract v_9886 32 64);
      v_9895 <- eval (extract v_9889 32 64);
      v_9899 <- eval (extract v_9886 64 96);
      v_9900 <- eval (extract v_9889 64 96);
      v_9904 <- eval (extract v_9886 96 128);
      v_9905 <- eval (extract v_9889 96 128);
      setRegister (lhs.of_reg v_2621) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9887 v_9890) (expression.bv_nat 1 1)) v_9887 v_9890) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9894 v_9895) (expression.bv_nat 1 1)) v_9894 v_9895) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9899 v_9900) (expression.bv_nat 1 1)) v_9899 v_9900) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9904 v_9905) (expression.bv_nat 1 1)) v_9904 v_9905))));
      pure ()
    pat_end;
    pattern fun (v_2630 : Mem) (v_2631 : reg (bv 256)) (v_2632 : reg (bv 256)) => do
      v_9913 <- getRegister v_2631;
      v_9914 <- eval (extract v_9913 0 32);
      v_9915 <- evaluateAddress v_2630;
      v_9916 <- load v_9915 32;
      v_9917 <- eval (extract v_9916 0 32);
      v_9921 <- eval (extract v_9913 32 64);
      v_9922 <- eval (extract v_9916 32 64);
      v_9926 <- eval (extract v_9913 64 96);
      v_9927 <- eval (extract v_9916 64 96);
      v_9931 <- eval (extract v_9913 96 128);
      v_9932 <- eval (extract v_9916 96 128);
      v_9936 <- eval (extract v_9913 128 160);
      v_9937 <- eval (extract v_9916 128 160);
      v_9941 <- eval (extract v_9913 160 192);
      v_9942 <- eval (extract v_9916 160 192);
      v_9946 <- eval (extract v_9913 192 224);
      v_9947 <- eval (extract v_9916 192 224);
      v_9951 <- eval (extract v_9913 224 256);
      v_9952 <- eval (extract v_9916 224 256);
      setRegister (lhs.of_reg v_2632) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9914 v_9917) (expression.bv_nat 1 1)) v_9914 v_9917) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9921 v_9922) (expression.bv_nat 1 1)) v_9921 v_9922) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9926 v_9927) (expression.bv_nat 1 1)) v_9926 v_9927) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9931 v_9932) (expression.bv_nat 1 1)) v_9931 v_9932) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9936 v_9937) (expression.bv_nat 1 1)) v_9936 v_9937) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9941 v_9942) (expression.bv_nat 1 1)) v_9941 v_9942) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9946 v_9947) (expression.bv_nat 1 1)) v_9946 v_9947) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9951 v_9952) (expression.bv_nat 1 1)) v_9951 v_9952))))))));
      pure ()
    pat_end
