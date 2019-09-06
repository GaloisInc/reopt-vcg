def vmaxpd1 : instruction :=
  definst "vmaxpd" $ do
    pattern fun (v_2627 : reg (bv 128)) (v_2628 : reg (bv 128)) (v_2629 : reg (bv 128)) => do
      v_4403 <- getRegister v_2628;
      v_4404 <- eval (extract v_4403 0 64);
      v_4405 <- getRegister v_2627;
      v_4406 <- eval (extract v_4405 0 64);
      v_4410 <- eval (extract v_4403 64 128);
      v_4411 <- eval (extract v_4405 64 128);
      setRegister (lhs.of_reg v_2629) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4404 v_4406) (expression.bv_nat 1 1)) v_4404 v_4406) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4410 v_4411) (expression.bv_nat 1 1)) v_4410 v_4411));
      pure ()
    pat_end;
    pattern fun (v_2638 : reg (bv 256)) (v_2639 : reg (bv 256)) (v_2640 : reg (bv 256)) => do
      v_4422 <- getRegister v_2639;
      v_4423 <- eval (extract v_4422 0 64);
      v_4424 <- getRegister v_2638;
      v_4425 <- eval (extract v_4424 0 64);
      v_4429 <- eval (extract v_4422 64 128);
      v_4430 <- eval (extract v_4424 64 128);
      v_4434 <- eval (extract v_4422 128 192);
      v_4435 <- eval (extract v_4424 128 192);
      v_4439 <- eval (extract v_4422 192 256);
      v_4440 <- eval (extract v_4424 192 256);
      setRegister (lhs.of_reg v_2640) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4423 v_4425) (expression.bv_nat 1 1)) v_4423 v_4425) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4429 v_4430) (expression.bv_nat 1 1)) v_4429 v_4430) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4434 v_4435) (expression.bv_nat 1 1)) v_4434 v_4435) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4439 v_4440) (expression.bv_nat 1 1)) v_4439 v_4440))));
      pure ()
    pat_end;
    pattern fun (v_2622 : Mem) (v_2623 : reg (bv 128)) (v_2624 : reg (bv 128)) => do
      v_9871 <- getRegister v_2623;
      v_9872 <- eval (extract v_9871 0 64);
      v_9873 <- evaluateAddress v_2622;
      v_9874 <- load v_9873 16;
      v_9875 <- eval (extract v_9874 0 64);
      v_9879 <- eval (extract v_9871 64 128);
      v_9880 <- eval (extract v_9874 64 128);
      setRegister (lhs.of_reg v_2624) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9872 v_9875) (expression.bv_nat 1 1)) v_9872 v_9875) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9879 v_9880) (expression.bv_nat 1 1)) v_9879 v_9880));
      pure ()
    pat_end;
    pattern fun (v_2633 : Mem) (v_2634 : reg (bv 256)) (v_2635 : reg (bv 256)) => do
      v_9886 <- getRegister v_2634;
      v_9887 <- eval (extract v_9886 0 64);
      v_9888 <- evaluateAddress v_2633;
      v_9889 <- load v_9888 32;
      v_9890 <- eval (extract v_9889 0 64);
      v_9894 <- eval (extract v_9886 64 128);
      v_9895 <- eval (extract v_9889 64 128);
      v_9899 <- eval (extract v_9886 128 192);
      v_9900 <- eval (extract v_9889 128 192);
      v_9904 <- eval (extract v_9886 192 256);
      v_9905 <- eval (extract v_9889 192 256);
      setRegister (lhs.of_reg v_2635) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9887 v_9890) (expression.bv_nat 1 1)) v_9887 v_9890) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9894 v_9895) (expression.bv_nat 1 1)) v_9894 v_9895) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9899 v_9900) (expression.bv_nat 1 1)) v_9899 v_9900) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_9904 v_9905) (expression.bv_nat 1 1)) v_9904 v_9905))));
      pure ()
    pat_end
