def vminss1 : instruction :=
  definst "vminss" $ do
    pattern fun (v_2672 : reg (bv 128)) (v_2673 : reg (bv 128)) (v_2674 : reg (bv 128)) => do
      v_5008 <- getRegister v_2673;
      v_5010 <- eval (extract v_5008 96 128);
      v_5011 <- getRegister v_2672;
      v_5012 <- eval (extract v_5011 96 128);
      setRegister (lhs.of_reg v_2674) (concat (extract v_5008 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_5010 v_5012) (expression.bv_nat 1 1)) v_5010 v_5012));
      pure ()
    pat_end;
    pattern fun (v_2667 : Mem) (v_2668 : reg (bv 128)) (v_2669 : reg (bv 128)) => do
      v_11053 <- getRegister v_2668;
      v_11055 <- eval (extract v_11053 96 128);
      v_11056 <- evaluateAddress v_2667;
      v_11057 <- load v_11056 4;
      setRegister (lhs.of_reg v_2669) (concat (extract v_11053 0 96) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_11055 v_11057) (expression.bv_nat 1 1)) v_11055 v_11057));
      pure ()
    pat_end
