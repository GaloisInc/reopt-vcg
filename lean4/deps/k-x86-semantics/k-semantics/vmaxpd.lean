def vmaxpd1 : instruction :=
  definst "vmaxpd" $ do
    pattern fun (v_2551 : reg (bv 128)) (v_2552 : reg (bv 128)) (v_2553 : reg (bv 128)) => do
      v_4691 <- getRegister v_2552;
      v_4692 <- eval (extract v_4691 0 64);
      v_4693 <- getRegister v_2551;
      v_4694 <- eval (extract v_4693 0 64);
      v_4698 <- eval (extract v_4691 64 128);
      v_4699 <- eval (extract v_4693 64 128);
      setRegister (lhs.of_reg v_2553) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4692 v_4694) (expression.bv_nat 1 1)) v_4692 v_4694) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4698 v_4699) (expression.bv_nat 1 1)) v_4698 v_4699));
      pure ()
    pat_end;
    pattern fun (v_2562 : reg (bv 256)) (v_2563 : reg (bv 256)) (v_2564 : reg (bv 256)) => do
      v_4710 <- getRegister v_2563;
      v_4711 <- eval (extract v_4710 0 64);
      v_4712 <- getRegister v_2562;
      v_4713 <- eval (extract v_4712 0 64);
      v_4717 <- eval (extract v_4710 64 128);
      v_4718 <- eval (extract v_4712 64 128);
      v_4722 <- eval (extract v_4710 128 192);
      v_4723 <- eval (extract v_4712 128 192);
      v_4727 <- eval (extract v_4710 192 256);
      v_4728 <- eval (extract v_4712 192 256);
      setRegister (lhs.of_reg v_2564) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4711 v_4713) (expression.bv_nat 1 1)) v_4711 v_4713) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4717 v_4718) (expression.bv_nat 1 1)) v_4717 v_4718) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4722 v_4723) (expression.bv_nat 1 1)) v_4722 v_4723) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_4727 v_4728) (expression.bv_nat 1 1)) v_4727 v_4728))));
      pure ()
    pat_end;
    pattern fun (v_2546 : Mem) (v_2547 : reg (bv 128)) (v_2548 : reg (bv 128)) => do
      v_10783 <- getRegister v_2547;
      v_10784 <- eval (extract v_10783 0 64);
      v_10785 <- evaluateAddress v_2546;
      v_10786 <- load v_10785 16;
      v_10787 <- eval (extract v_10786 0 64);
      v_10791 <- eval (extract v_10783 64 128);
      v_10792 <- eval (extract v_10786 64 128);
      setRegister (lhs.of_reg v_2548) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10784 v_10787) (expression.bv_nat 1 1)) v_10784 v_10787) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10791 v_10792) (expression.bv_nat 1 1)) v_10791 v_10792));
      pure ()
    pat_end;
    pattern fun (v_2557 : Mem) (v_2558 : reg (bv 256)) (v_2559 : reg (bv 256)) => do
      v_10798 <- getRegister v_2558;
      v_10799 <- eval (extract v_10798 0 64);
      v_10800 <- evaluateAddress v_2557;
      v_10801 <- load v_10800 32;
      v_10802 <- eval (extract v_10801 0 64);
      v_10806 <- eval (extract v_10798 64 128);
      v_10807 <- eval (extract v_10801 64 128);
      v_10811 <- eval (extract v_10798 128 192);
      v_10812 <- eval (extract v_10801 128 192);
      v_10816 <- eval (extract v_10798 192 256);
      v_10817 <- eval (extract v_10801 192 256);
      setRegister (lhs.of_reg v_2559) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10799 v_10802) (expression.bv_nat 1 1)) v_10799 v_10802) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10806 v_10807) (expression.bv_nat 1 1)) v_10806 v_10807) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10811 v_10812) (expression.bv_nat 1 1)) v_10811 v_10812) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_double v_10816 v_10817) (expression.bv_nat 1 1)) v_10816 v_10817))));
      pure ()
    pat_end
