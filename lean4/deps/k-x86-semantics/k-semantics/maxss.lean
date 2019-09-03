def maxss1 : instruction :=
  definst "maxss" $ do
    pattern fun (v_3078 : reg (bv 128)) (v_3079 : reg (bv 128)) => do
      v_5791 <- getRegister v_3079;
      v_5793 <- eval (extract v_5791 96 128);
      v_5794 <- getRegister v_3078;
      v_5795 <- eval (extract v_5794 96 128);
      setRegister (lhs.of_reg v_3079) (concat (extract v_5791 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_5793 v_5795) (expression.bv_nat 1 1)) v_5793 v_5795));
      pure ()
    pat_end;
    pattern fun (v_3074 : Mem) (v_3075 : reg (bv 128)) => do
      v_9234 <- getRegister v_3075;
      v_9236 <- eval (extract v_9234 96 128);
      v_9237 <- evaluateAddress v_3074;
      v_9238 <- load v_9237 4;
      setRegister (lhs.of_reg v_3075) (concat (extract v_9234 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX maxcmp_single v_9236 v_9238) (expression.bv_nat 1 1)) v_9236 v_9238));
      pure ()
    pat_end
