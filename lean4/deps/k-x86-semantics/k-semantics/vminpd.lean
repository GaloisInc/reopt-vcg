def vminpd1 : instruction :=
  definst "vminpd" $ do
    pattern fun (v_2693 : reg (bv 128)) (v_2694 : reg (bv 128)) (v_2695 : reg (bv 128)) => do
      v_4569 <- getRegister v_2694;
      v_4570 <- eval (extract v_4569 0 64);
      v_4571 <- getRegister v_2693;
      v_4572 <- eval (extract v_4571 0 64);
      v_4576 <- eval (extract v_4569 64 128);
      v_4577 <- eval (extract v_4571 64 128);
      setRegister (lhs.of_reg v_2695) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4570 v_4572) (expression.bv_nat 1 1)) v_4570 v_4572) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4576 v_4577) (expression.bv_nat 1 1)) v_4576 v_4577));
      pure ()
    pat_end;
    pattern fun (v_2704 : reg (bv 256)) (v_2705 : reg (bv 256)) (v_2706 : reg (bv 256)) => do
      v_4588 <- getRegister v_2705;
      v_4589 <- eval (extract v_4588 0 64);
      v_4590 <- getRegister v_2704;
      v_4591 <- eval (extract v_4590 0 64);
      v_4595 <- eval (extract v_4588 64 128);
      v_4596 <- eval (extract v_4590 64 128);
      v_4600 <- eval (extract v_4588 128 192);
      v_4601 <- eval (extract v_4590 128 192);
      v_4605 <- eval (extract v_4588 192 256);
      v_4606 <- eval (extract v_4590 192 256);
      setRegister (lhs.of_reg v_2706) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4589 v_4591) (expression.bv_nat 1 1)) v_4589 v_4591) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4595 v_4596) (expression.bv_nat 1 1)) v_4595 v_4596) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4600 v_4601) (expression.bv_nat 1 1)) v_4600 v_4601) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_4605 v_4606) (expression.bv_nat 1 1)) v_4605 v_4606))));
      pure ()
    pat_end;
    pattern fun (v_2688 : Mem) (v_2689 : reg (bv 128)) (v_2690 : reg (bv 128)) => do
      v_10011 <- getRegister v_2689;
      v_10012 <- eval (extract v_10011 0 64);
      v_10013 <- evaluateAddress v_2688;
      v_10014 <- load v_10013 16;
      v_10015 <- eval (extract v_10014 0 64);
      v_10019 <- eval (extract v_10011 64 128);
      v_10020 <- eval (extract v_10014 64 128);
      setRegister (lhs.of_reg v_2690) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10012 v_10015) (expression.bv_nat 1 1)) v_10012 v_10015) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10019 v_10020) (expression.bv_nat 1 1)) v_10019 v_10020));
      pure ()
    pat_end;
    pattern fun (v_2699 : Mem) (v_2700 : reg (bv 256)) (v_2701 : reg (bv 256)) => do
      v_10026 <- getRegister v_2700;
      v_10027 <- eval (extract v_10026 0 64);
      v_10028 <- evaluateAddress v_2699;
      v_10029 <- load v_10028 32;
      v_10030 <- eval (extract v_10029 0 64);
      v_10034 <- eval (extract v_10026 64 128);
      v_10035 <- eval (extract v_10029 64 128);
      v_10039 <- eval (extract v_10026 128 192);
      v_10040 <- eval (extract v_10029 128 192);
      v_10044 <- eval (extract v_10026 192 256);
      v_10045 <- eval (extract v_10029 192 256);
      setRegister (lhs.of_reg v_2701) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10027 v_10030) (expression.bv_nat 1 1)) v_10027 v_10030) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10034 v_10035) (expression.bv_nat 1 1)) v_10034 v_10035) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10039 v_10040) (expression.bv_nat 1 1)) v_10039 v_10040) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_double v_10044 v_10045) (expression.bv_nat 1 1)) v_10044 v_10045))));
      pure ()
    pat_end
