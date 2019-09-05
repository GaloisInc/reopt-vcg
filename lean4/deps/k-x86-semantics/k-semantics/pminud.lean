def pminud1 : instruction :=
  definst "pminud" $ do
    pattern fun (v_2701 : reg (bv 128)) (v_2702 : reg (bv 128)) => do
      v_5292 <- getRegister v_2702;
      v_5293 <- eval (extract v_5292 0 32);
      v_5294 <- getRegister v_2701;
      v_5295 <- eval (extract v_5294 0 32);
      v_5298 <- eval (extract v_5292 32 64);
      v_5299 <- eval (extract v_5294 32 64);
      v_5302 <- eval (extract v_5292 64 96);
      v_5303 <- eval (extract v_5294 64 96);
      v_5306 <- eval (extract v_5292 96 128);
      v_5307 <- eval (extract v_5294 96 128);
      setRegister (lhs.of_reg v_2702) (concat (mux (ult v_5293 v_5295) v_5293 v_5295) (concat (mux (ult v_5298 v_5299) v_5298 v_5299) (concat (mux (ult v_5302 v_5303) v_5302 v_5303) (mux (ult v_5306 v_5307) v_5306 v_5307))));
      pure ()
    pat_end;
    pattern fun (v_2698 : Mem) (v_2697 : reg (bv 128)) => do
      v_12166 <- getRegister v_2697;
      v_12167 <- eval (extract v_12166 0 32);
      v_12168 <- evaluateAddress v_2698;
      v_12169 <- load v_12168 16;
      v_12170 <- eval (extract v_12169 0 32);
      v_12173 <- eval (extract v_12166 32 64);
      v_12174 <- eval (extract v_12169 32 64);
      v_12177 <- eval (extract v_12166 64 96);
      v_12178 <- eval (extract v_12169 64 96);
      v_12181 <- eval (extract v_12166 96 128);
      v_12182 <- eval (extract v_12169 96 128);
      setRegister (lhs.of_reg v_2697) (concat (mux (ult v_12167 v_12170) v_12167 v_12170) (concat (mux (ult v_12173 v_12174) v_12173 v_12174) (concat (mux (ult v_12177 v_12178) v_12177 v_12178) (mux (ult v_12181 v_12182) v_12181 v_12182))));
      pure ()
    pat_end
