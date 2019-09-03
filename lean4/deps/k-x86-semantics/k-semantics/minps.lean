def minps1 : instruction :=
  definst "minps" $ do
    pattern fun (v_3096 : reg (bv 128)) (v_3097 : reg (bv 128)) => do
      v_5823 <- getRegister v_3097;
      v_5824 <- eval (extract v_5823 0 32);
      v_5825 <- getRegister v_3096;
      v_5826 <- eval (extract v_5825 0 32);
      v_5830 <- eval (extract v_5823 32 64);
      v_5831 <- eval (extract v_5825 32 64);
      v_5835 <- eval (extract v_5823 64 96);
      v_5836 <- eval (extract v_5825 64 96);
      v_5840 <- eval (extract v_5823 96 128);
      v_5841 <- eval (extract v_5825 96 128);
      setRegister (lhs.of_reg v_3097) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5824 v_5826) (expression.bv_nat 1 1)) v_5824 v_5826) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5830 v_5831) (expression.bv_nat 1 1)) v_5830 v_5831) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5835 v_5836) (expression.bv_nat 1 1)) v_5835 v_5836) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5840 v_5841) (expression.bv_nat 1 1)) v_5840 v_5841))));
      pure ()
    pat_end;
    pattern fun (v_3092 : Mem) (v_3093 : reg (bv 128)) => do
      v_9259 <- getRegister v_3093;
      v_9260 <- eval (extract v_9259 0 32);
      v_9261 <- evaluateAddress v_3092;
      v_9262 <- load v_9261 16;
      v_9263 <- eval (extract v_9262 0 32);
      v_9267 <- eval (extract v_9259 32 64);
      v_9268 <- eval (extract v_9262 32 64);
      v_9272 <- eval (extract v_9259 64 96);
      v_9273 <- eval (extract v_9262 64 96);
      v_9277 <- eval (extract v_9259 96 128);
      v_9278 <- eval (extract v_9262 96 128);
      setRegister (lhs.of_reg v_3093) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9260 v_9263) (expression.bv_nat 1 1)) v_9260 v_9263) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9267 v_9268) (expression.bv_nat 1 1)) v_9267 v_9268) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9272 v_9273) (expression.bv_nat 1 1)) v_9272 v_9273) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_9277 v_9278) (expression.bv_nat 1 1)) v_9277 v_9278))));
      pure ()
    pat_end
