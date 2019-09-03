def vminps1 : instruction :=
  definst "vminps" $ do
    pattern fun (v_2639 : reg (bv 128)) (v_2640 : reg (bv 128)) (v_2641 : reg (bv 128)) => do
      v_4907 <- getRegister v_2640;
      v_4908 <- eval (extract v_4907 0 32);
      v_4909 <- getRegister v_2639;
      v_4910 <- eval (extract v_4909 0 32);
      v_4914 <- eval (extract v_4907 32 64);
      v_4915 <- eval (extract v_4909 32 64);
      v_4919 <- eval (extract v_4907 64 96);
      v_4920 <- eval (extract v_4909 64 96);
      v_4924 <- eval (extract v_4907 96 128);
      v_4925 <- eval (extract v_4909 96 128);
      setRegister (lhs.of_reg v_2641) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4908 v_4910) (expression.bv_nat 1 1)) v_4908 v_4910) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4914 v_4915) (expression.bv_nat 1 1)) v_4914 v_4915) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4919 v_4920) (expression.bv_nat 1 1)) v_4919 v_4920) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4924 v_4925) (expression.bv_nat 1 1)) v_4924 v_4925))));
      pure ()
    pat_end;
    pattern fun (v_2650 : reg (bv 256)) (v_2651 : reg (bv 256)) (v_2652 : reg (bv 256)) => do
      v_4938 <- getRegister v_2651;
      v_4939 <- eval (extract v_4938 0 32);
      v_4940 <- getRegister v_2650;
      v_4941 <- eval (extract v_4940 0 32);
      v_4945 <- eval (extract v_4938 32 64);
      v_4946 <- eval (extract v_4940 32 64);
      v_4950 <- eval (extract v_4938 64 96);
      v_4951 <- eval (extract v_4940 64 96);
      v_4955 <- eval (extract v_4938 96 128);
      v_4956 <- eval (extract v_4940 96 128);
      v_4960 <- eval (extract v_4938 128 160);
      v_4961 <- eval (extract v_4940 128 160);
      v_4965 <- eval (extract v_4938 160 192);
      v_4966 <- eval (extract v_4940 160 192);
      v_4970 <- eval (extract v_4938 192 224);
      v_4971 <- eval (extract v_4940 192 224);
      v_4975 <- eval (extract v_4938 224 256);
      v_4976 <- eval (extract v_4940 224 256);
      setRegister (lhs.of_reg v_2652) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4939 v_4941) (expression.bv_nat 1 1)) v_4939 v_4941) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4945 v_4946) (expression.bv_nat 1 1)) v_4945 v_4946) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4950 v_4951) (expression.bv_nat 1 1)) v_4950 v_4951) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4955 v_4956) (expression.bv_nat 1 1)) v_4955 v_4956) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4960 v_4961) (expression.bv_nat 1 1)) v_4960 v_4961) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4965 v_4966) (expression.bv_nat 1 1)) v_4965 v_4966) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4970 v_4971) (expression.bv_nat 1 1)) v_4970 v_4971) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4975 v_4976) (expression.bv_nat 1 1)) v_4975 v_4976))))))));
      pure ()
    pat_end;
    pattern fun (v_2634 : Mem) (v_2635 : reg (bv 128)) (v_2636 : reg (bv 128)) => do
      v_10965 <- getRegister v_2635;
      v_10966 <- eval (extract v_10965 0 32);
      v_10967 <- evaluateAddress v_2634;
      v_10968 <- load v_10967 16;
      v_10969 <- eval (extract v_10968 0 32);
      v_10973 <- eval (extract v_10965 32 64);
      v_10974 <- eval (extract v_10968 32 64);
      v_10978 <- eval (extract v_10965 64 96);
      v_10979 <- eval (extract v_10968 64 96);
      v_10983 <- eval (extract v_10965 96 128);
      v_10984 <- eval (extract v_10968 96 128);
      setRegister (lhs.of_reg v_2636) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10966 v_10969) (expression.bv_nat 1 1)) v_10966 v_10969) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10973 v_10974) (expression.bv_nat 1 1)) v_10973 v_10974) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10978 v_10979) (expression.bv_nat 1 1)) v_10978 v_10979) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10983 v_10984) (expression.bv_nat 1 1)) v_10983 v_10984))));
      pure ()
    pat_end;
    pattern fun (v_2645 : Mem) (v_2646 : reg (bv 256)) (v_2647 : reg (bv 256)) => do
      v_10992 <- getRegister v_2646;
      v_10993 <- eval (extract v_10992 0 32);
      v_10994 <- evaluateAddress v_2645;
      v_10995 <- load v_10994 32;
      v_10996 <- eval (extract v_10995 0 32);
      v_11000 <- eval (extract v_10992 32 64);
      v_11001 <- eval (extract v_10995 32 64);
      v_11005 <- eval (extract v_10992 64 96);
      v_11006 <- eval (extract v_10995 64 96);
      v_11010 <- eval (extract v_10992 96 128);
      v_11011 <- eval (extract v_10995 96 128);
      v_11015 <- eval (extract v_10992 128 160);
      v_11016 <- eval (extract v_10995 128 160);
      v_11020 <- eval (extract v_10992 160 192);
      v_11021 <- eval (extract v_10995 160 192);
      v_11025 <- eval (extract v_10992 192 224);
      v_11026 <- eval (extract v_10995 192 224);
      v_11030 <- eval (extract v_10992 224 256);
      v_11031 <- eval (extract v_10995 224 256);
      setRegister (lhs.of_reg v_2647) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10993 v_10996) (expression.bv_nat 1 1)) v_10993 v_10996) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11000 v_11001) (expression.bv_nat 1 1)) v_11000 v_11001) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11005 v_11006) (expression.bv_nat 1 1)) v_11005 v_11006) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11010 v_11011) (expression.bv_nat 1 1)) v_11010 v_11011) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11015 v_11016) (expression.bv_nat 1 1)) v_11015 v_11016) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11020 v_11021) (expression.bv_nat 1 1)) v_11020 v_11021) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11025 v_11026) (expression.bv_nat 1 1)) v_11025 v_11026) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11030 v_11031) (expression.bv_nat 1 1)) v_11030 v_11031))))))));
      pure ()
    pat_end
