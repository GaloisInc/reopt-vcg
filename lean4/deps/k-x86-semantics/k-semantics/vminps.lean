def vminps1 : instruction :=
  definst "vminps" $ do
    pattern fun (v_2715 : reg (bv 128)) (v_2716 : reg (bv 128)) (v_2717 : reg (bv 128)) => do
      v_4619 <- getRegister v_2716;
      v_4620 <- eval (extract v_4619 0 32);
      v_4621 <- getRegister v_2715;
      v_4622 <- eval (extract v_4621 0 32);
      v_4626 <- eval (extract v_4619 32 64);
      v_4627 <- eval (extract v_4621 32 64);
      v_4631 <- eval (extract v_4619 64 96);
      v_4632 <- eval (extract v_4621 64 96);
      v_4636 <- eval (extract v_4619 96 128);
      v_4637 <- eval (extract v_4621 96 128);
      setRegister (lhs.of_reg v_2717) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4620 v_4622) (expression.bv_nat 1 1)) v_4620 v_4622) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4626 v_4627) (expression.bv_nat 1 1)) v_4626 v_4627) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4631 v_4632) (expression.bv_nat 1 1)) v_4631 v_4632) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4636 v_4637) (expression.bv_nat 1 1)) v_4636 v_4637))));
      pure ()
    pat_end;
    pattern fun (v_2726 : reg (bv 256)) (v_2727 : reg (bv 256)) (v_2728 : reg (bv 256)) => do
      v_4650 <- getRegister v_2727;
      v_4651 <- eval (extract v_4650 0 32);
      v_4652 <- getRegister v_2726;
      v_4653 <- eval (extract v_4652 0 32);
      v_4657 <- eval (extract v_4650 32 64);
      v_4658 <- eval (extract v_4652 32 64);
      v_4662 <- eval (extract v_4650 64 96);
      v_4663 <- eval (extract v_4652 64 96);
      v_4667 <- eval (extract v_4650 96 128);
      v_4668 <- eval (extract v_4652 96 128);
      v_4672 <- eval (extract v_4650 128 160);
      v_4673 <- eval (extract v_4652 128 160);
      v_4677 <- eval (extract v_4650 160 192);
      v_4678 <- eval (extract v_4652 160 192);
      v_4682 <- eval (extract v_4650 192 224);
      v_4683 <- eval (extract v_4652 192 224);
      v_4687 <- eval (extract v_4650 224 256);
      v_4688 <- eval (extract v_4652 224 256);
      setRegister (lhs.of_reg v_2728) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4651 v_4653) (expression.bv_nat 1 1)) v_4651 v_4653) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4657 v_4658) (expression.bv_nat 1 1)) v_4657 v_4658) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4662 v_4663) (expression.bv_nat 1 1)) v_4662 v_4663) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4667 v_4668) (expression.bv_nat 1 1)) v_4667 v_4668) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4672 v_4673) (expression.bv_nat 1 1)) v_4672 v_4673) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4677 v_4678) (expression.bv_nat 1 1)) v_4677 v_4678) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4682 v_4683) (expression.bv_nat 1 1)) v_4682 v_4683) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4687 v_4688) (expression.bv_nat 1 1)) v_4687 v_4688))))))));
      pure ()
    pat_end;
    pattern fun (v_2710 : Mem) (v_2711 : reg (bv 128)) (v_2712 : reg (bv 128)) => do
      v_10053 <- getRegister v_2711;
      v_10054 <- eval (extract v_10053 0 32);
      v_10055 <- evaluateAddress v_2710;
      v_10056 <- load v_10055 16;
      v_10057 <- eval (extract v_10056 0 32);
      v_10061 <- eval (extract v_10053 32 64);
      v_10062 <- eval (extract v_10056 32 64);
      v_10066 <- eval (extract v_10053 64 96);
      v_10067 <- eval (extract v_10056 64 96);
      v_10071 <- eval (extract v_10053 96 128);
      v_10072 <- eval (extract v_10056 96 128);
      setRegister (lhs.of_reg v_2712) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10054 v_10057) (expression.bv_nat 1 1)) v_10054 v_10057) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10061 v_10062) (expression.bv_nat 1 1)) v_10061 v_10062) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10066 v_10067) (expression.bv_nat 1 1)) v_10066 v_10067) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10071 v_10072) (expression.bv_nat 1 1)) v_10071 v_10072))));
      pure ()
    pat_end;
    pattern fun (v_2721 : Mem) (v_2722 : reg (bv 256)) (v_2723 : reg (bv 256)) => do
      v_10080 <- getRegister v_2722;
      v_10081 <- eval (extract v_10080 0 32);
      v_10082 <- evaluateAddress v_2721;
      v_10083 <- load v_10082 32;
      v_10084 <- eval (extract v_10083 0 32);
      v_10088 <- eval (extract v_10080 32 64);
      v_10089 <- eval (extract v_10083 32 64);
      v_10093 <- eval (extract v_10080 64 96);
      v_10094 <- eval (extract v_10083 64 96);
      v_10098 <- eval (extract v_10080 96 128);
      v_10099 <- eval (extract v_10083 96 128);
      v_10103 <- eval (extract v_10080 128 160);
      v_10104 <- eval (extract v_10083 128 160);
      v_10108 <- eval (extract v_10080 160 192);
      v_10109 <- eval (extract v_10083 160 192);
      v_10113 <- eval (extract v_10080 192 224);
      v_10114 <- eval (extract v_10083 192 224);
      v_10118 <- eval (extract v_10080 224 256);
      v_10119 <- eval (extract v_10083 224 256);
      setRegister (lhs.of_reg v_2723) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10081 v_10084) (expression.bv_nat 1 1)) v_10081 v_10084) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10088 v_10089) (expression.bv_nat 1 1)) v_10088 v_10089) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10093 v_10094) (expression.bv_nat 1 1)) v_10093 v_10094) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10098 v_10099) (expression.bv_nat 1 1)) v_10098 v_10099) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10103 v_10104) (expression.bv_nat 1 1)) v_10103 v_10104) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10108 v_10109) (expression.bv_nat 1 1)) v_10108 v_10109) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10113 v_10114) (expression.bv_nat 1 1)) v_10113 v_10114) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10118 v_10119) (expression.bv_nat 1 1)) v_10118 v_10119))))))));
      pure ()
    pat_end
