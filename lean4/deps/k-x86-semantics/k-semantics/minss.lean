def minss1 : instruction :=
  definst "minss" $ do
    pattern fun (v_3114 : reg (bv 128)) (v_3115 : reg (bv 128)) => do
      v_5867 <- getRegister v_3115;
      v_5869 <- eval (extract v_5867 96 128);
      v_5870 <- getRegister v_3114;
      v_5871 <- eval (extract v_5870 96 128);
      setRegister (lhs.of_reg v_3115) (concat (extract v_5867 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5869 v_5871) (expression.bv_nat 1 1)) v_5869 v_5871));
      pure ()
    pat_end;
    pattern fun (v_3110 : Mem) (v_3111 : reg (bv 128)) => do
      v_9296 <- getRegister v_3111;
      v_9298 <- eval (extract v_9296 96 128);
      v_9299 <- evaluateAddress v_3110;
      v_9300 <- load v_9299 4;
      setRegister (lhs.of_reg v_3111) (concat (extract v_9296 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9298 v_9300) (expression.bv_nat 1 1)) v_9298 v_9300));
      pure ()
    pat_end
