def vmaxps1 : instruction :=
  definst "vmaxps" $ do
    pattern fun (v_2573 : reg (bv 128)) (v_2574 : reg (bv 128)) (v_2575 : reg (bv 128)) => do
      v_4741 <- getRegister v_2574;
      v_4742 <- eval (extract v_4741 0 32);
      v_4743 <- getRegister v_2573;
      v_4744 <- eval (extract v_4743 0 32);
      v_4748 <- eval (extract v_4741 32 64);
      v_4749 <- eval (extract v_4743 32 64);
      v_4753 <- eval (extract v_4741 64 96);
      v_4754 <- eval (extract v_4743 64 96);
      v_4758 <- eval (extract v_4741 96 128);
      v_4759 <- eval (extract v_4743 96 128);
      setRegister (lhs.of_reg v_2575) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4742 v_4744) (expression.bv_nat 1 1)) v_4742 v_4744) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4748 v_4749) (expression.bv_nat 1 1)) v_4748 v_4749) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4753 v_4754) (expression.bv_nat 1 1)) v_4753 v_4754) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4758 v_4759) (expression.bv_nat 1 1)) v_4758 v_4759))));
      pure ()
    pat_end;
    pattern fun (v_2584 : reg (bv 256)) (v_2585 : reg (bv 256)) (v_2586 : reg (bv 256)) => do
      v_4772 <- getRegister v_2585;
      v_4773 <- eval (extract v_4772 0 32);
      v_4774 <- getRegister v_2584;
      v_4775 <- eval (extract v_4774 0 32);
      v_4779 <- eval (extract v_4772 32 64);
      v_4780 <- eval (extract v_4774 32 64);
      v_4784 <- eval (extract v_4772 64 96);
      v_4785 <- eval (extract v_4774 64 96);
      v_4789 <- eval (extract v_4772 96 128);
      v_4790 <- eval (extract v_4774 96 128);
      v_4794 <- eval (extract v_4772 128 160);
      v_4795 <- eval (extract v_4774 128 160);
      v_4799 <- eval (extract v_4772 160 192);
      v_4800 <- eval (extract v_4774 160 192);
      v_4804 <- eval (extract v_4772 192 224);
      v_4805 <- eval (extract v_4774 192 224);
      v_4809 <- eval (extract v_4772 224 256);
      v_4810 <- eval (extract v_4774 224 256);
      setRegister (lhs.of_reg v_2586) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4773 v_4775) (expression.bv_nat 1 1)) v_4773 v_4775) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4779 v_4780) (expression.bv_nat 1 1)) v_4779 v_4780) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4784 v_4785) (expression.bv_nat 1 1)) v_4784 v_4785) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4789 v_4790) (expression.bv_nat 1 1)) v_4789 v_4790) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4794 v_4795) (expression.bv_nat 1 1)) v_4794 v_4795) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4799 v_4800) (expression.bv_nat 1 1)) v_4799 v_4800) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4804 v_4805) (expression.bv_nat 1 1)) v_4804 v_4805) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_4809 v_4810) (expression.bv_nat 1 1)) v_4809 v_4810))))))));
      pure ()
    pat_end;
    pattern fun (v_2568 : Mem) (v_2569 : reg (bv 128)) (v_2570 : reg (bv 128)) => do
      v_10825 <- getRegister v_2569;
      v_10826 <- eval (extract v_10825 0 32);
      v_10827 <- evaluateAddress v_2568;
      v_10828 <- load v_10827 16;
      v_10829 <- eval (extract v_10828 0 32);
      v_10833 <- eval (extract v_10825 32 64);
      v_10834 <- eval (extract v_10828 32 64);
      v_10838 <- eval (extract v_10825 64 96);
      v_10839 <- eval (extract v_10828 64 96);
      v_10843 <- eval (extract v_10825 96 128);
      v_10844 <- eval (extract v_10828 96 128);
      setRegister (lhs.of_reg v_2570) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10826 v_10829) (expression.bv_nat 1 1)) v_10826 v_10829) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10833 v_10834) (expression.bv_nat 1 1)) v_10833 v_10834) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10838 v_10839) (expression.bv_nat 1 1)) v_10838 v_10839) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10843 v_10844) (expression.bv_nat 1 1)) v_10843 v_10844))));
      pure ()
    pat_end;
    pattern fun (v_2579 : Mem) (v_2580 : reg (bv 256)) (v_2581 : reg (bv 256)) => do
      v_10852 <- getRegister v_2580;
      v_10853 <- eval (extract v_10852 0 32);
      v_10854 <- evaluateAddress v_2579;
      v_10855 <- load v_10854 32;
      v_10856 <- eval (extract v_10855 0 32);
      v_10860 <- eval (extract v_10852 32 64);
      v_10861 <- eval (extract v_10855 32 64);
      v_10865 <- eval (extract v_10852 64 96);
      v_10866 <- eval (extract v_10855 64 96);
      v_10870 <- eval (extract v_10852 96 128);
      v_10871 <- eval (extract v_10855 96 128);
      v_10875 <- eval (extract v_10852 128 160);
      v_10876 <- eval (extract v_10855 128 160);
      v_10880 <- eval (extract v_10852 160 192);
      v_10881 <- eval (extract v_10855 160 192);
      v_10885 <- eval (extract v_10852 192 224);
      v_10886 <- eval (extract v_10855 192 224);
      v_10890 <- eval (extract v_10852 224 256);
      v_10891 <- eval (extract v_10855 224 256);
      setRegister (lhs.of_reg v_2581) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10853 v_10856) (expression.bv_nat 1 1)) v_10853 v_10856) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10860 v_10861) (expression.bv_nat 1 1)) v_10860 v_10861) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10865 v_10866) (expression.bv_nat 1 1)) v_10865 v_10866) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10870 v_10871) (expression.bv_nat 1 1)) v_10870 v_10871) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10875 v_10876) (expression.bv_nat 1 1)) v_10875 v_10876) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10880 v_10881) (expression.bv_nat 1 1)) v_10880 v_10881) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10885 v_10886) (expression.bv_nat 1 1)) v_10885 v_10886) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_10890 v_10891) (expression.bv_nat 1 1)) v_10890 v_10891))))))));
      pure ()
    pat_end
