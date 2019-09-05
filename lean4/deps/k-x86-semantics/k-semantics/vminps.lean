def vminps1 : instruction :=
  definst "vminps" $ do
    pattern fun (v_2690 : reg (bv 128)) (v_2691 : reg (bv 128)) (v_2692 : reg (bv 128)) => do
      v_4592 <- getRegister v_2691;
      v_4593 <- eval (extract v_4592 0 32);
      v_4594 <- getRegister v_2690;
      v_4595 <- eval (extract v_4594 0 32);
      v_4599 <- eval (extract v_4592 32 64);
      v_4600 <- eval (extract v_4594 32 64);
      v_4604 <- eval (extract v_4592 64 96);
      v_4605 <- eval (extract v_4594 64 96);
      v_4609 <- eval (extract v_4592 96 128);
      v_4610 <- eval (extract v_4594 96 128);
      setRegister (lhs.of_reg v_2692) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4593 v_4595) (expression.bv_nat 1 1)) v_4593 v_4595) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4599 v_4600) (expression.bv_nat 1 1)) v_4599 v_4600) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4604 v_4605) (expression.bv_nat 1 1)) v_4604 v_4605) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4609 v_4610) (expression.bv_nat 1 1)) v_4609 v_4610))));
      pure ()
    pat_end;
    pattern fun (v_2702 : reg (bv 256)) (v_2703 : reg (bv 256)) (v_2704 : reg (bv 256)) => do
      v_4623 <- getRegister v_2703;
      v_4624 <- eval (extract v_4623 0 32);
      v_4625 <- getRegister v_2702;
      v_4626 <- eval (extract v_4625 0 32);
      v_4630 <- eval (extract v_4623 32 64);
      v_4631 <- eval (extract v_4625 32 64);
      v_4635 <- eval (extract v_4623 64 96);
      v_4636 <- eval (extract v_4625 64 96);
      v_4640 <- eval (extract v_4623 96 128);
      v_4641 <- eval (extract v_4625 96 128);
      v_4645 <- eval (extract v_4623 128 160);
      v_4646 <- eval (extract v_4625 128 160);
      v_4650 <- eval (extract v_4623 160 192);
      v_4651 <- eval (extract v_4625 160 192);
      v_4655 <- eval (extract v_4623 192 224);
      v_4656 <- eval (extract v_4625 192 224);
      v_4660 <- eval (extract v_4623 224 256);
      v_4661 <- eval (extract v_4625 224 256);
      setRegister (lhs.of_reg v_2704) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4624 v_4626) (expression.bv_nat 1 1)) v_4624 v_4626) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4630 v_4631) (expression.bv_nat 1 1)) v_4630 v_4631) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4635 v_4636) (expression.bv_nat 1 1)) v_4635 v_4636) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4640 v_4641) (expression.bv_nat 1 1)) v_4640 v_4641) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4645 v_4646) (expression.bv_nat 1 1)) v_4645 v_4646) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4650 v_4651) (expression.bv_nat 1 1)) v_4650 v_4651) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4655 v_4656) (expression.bv_nat 1 1)) v_4655 v_4656) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4660 v_4661) (expression.bv_nat 1 1)) v_4660 v_4661))))))));
      pure ()
    pat_end;
    pattern fun (v_2685 : Mem) (v_2686 : reg (bv 128)) (v_2687 : reg (bv 128)) => do
      v_10026 <- getRegister v_2686;
      v_10027 <- eval (extract v_10026 0 32);
      v_10028 <- evaluateAddress v_2685;
      v_10029 <- load v_10028 16;
      v_10030 <- eval (extract v_10029 0 32);
      v_10034 <- eval (extract v_10026 32 64);
      v_10035 <- eval (extract v_10029 32 64);
      v_10039 <- eval (extract v_10026 64 96);
      v_10040 <- eval (extract v_10029 64 96);
      v_10044 <- eval (extract v_10026 96 128);
      v_10045 <- eval (extract v_10029 96 128);
      setRegister (lhs.of_reg v_2687) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10027 v_10030) (expression.bv_nat 1 1)) v_10027 v_10030) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10034 v_10035) (expression.bv_nat 1 1)) v_10034 v_10035) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10039 v_10040) (expression.bv_nat 1 1)) v_10039 v_10040) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10044 v_10045) (expression.bv_nat 1 1)) v_10044 v_10045))));
      pure ()
    pat_end;
    pattern fun (v_2696 : Mem) (v_2697 : reg (bv 256)) (v_2698 : reg (bv 256)) => do
      v_10053 <- getRegister v_2697;
      v_10054 <- eval (extract v_10053 0 32);
      v_10055 <- evaluateAddress v_2696;
      v_10056 <- load v_10055 32;
      v_10057 <- eval (extract v_10056 0 32);
      v_10061 <- eval (extract v_10053 32 64);
      v_10062 <- eval (extract v_10056 32 64);
      v_10066 <- eval (extract v_10053 64 96);
      v_10067 <- eval (extract v_10056 64 96);
      v_10071 <- eval (extract v_10053 96 128);
      v_10072 <- eval (extract v_10056 96 128);
      v_10076 <- eval (extract v_10053 128 160);
      v_10077 <- eval (extract v_10056 128 160);
      v_10081 <- eval (extract v_10053 160 192);
      v_10082 <- eval (extract v_10056 160 192);
      v_10086 <- eval (extract v_10053 192 224);
      v_10087 <- eval (extract v_10056 192 224);
      v_10091 <- eval (extract v_10053 224 256);
      v_10092 <- eval (extract v_10056 224 256);
      setRegister (lhs.of_reg v_2698) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10054 v_10057) (expression.bv_nat 1 1)) v_10054 v_10057) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10061 v_10062) (expression.bv_nat 1 1)) v_10061 v_10062) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10066 v_10067) (expression.bv_nat 1 1)) v_10066 v_10067) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10071 v_10072) (expression.bv_nat 1 1)) v_10071 v_10072) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10076 v_10077) (expression.bv_nat 1 1)) v_10076 v_10077) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10081 v_10082) (expression.bv_nat 1 1)) v_10081 v_10082) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10086 v_10087) (expression.bv_nat 1 1)) v_10086 v_10087) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10091 v_10092) (expression.bv_nat 1 1)) v_10091 v_10092))))))));
      pure ()
    pat_end
