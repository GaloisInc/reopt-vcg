def phaddsw1 : instruction :=
  definst "phaddsw" $ do
    pattern fun (v_2451 : reg (bv 128)) (v_2452 : reg (bv 128)) => do
      v_4064 <- getRegister v_2451;
      v_4069 <- eval (add (leanSignExtend (extract v_4064 0 16) 32) (leanSignExtend (extract v_4064 16 32) 32));
      v_4079 <- eval (add (leanSignExtend (extract v_4064 32 48) 32) (leanSignExtend (extract v_4064 48 64) 32));
      v_4089 <- eval (add (leanSignExtend (extract v_4064 64 80) 32) (leanSignExtend (extract v_4064 80 96) 32));
      v_4099 <- eval (add (leanSignExtend (extract v_4064 96 112) 32) (leanSignExtend (extract v_4064 112 128) 32));
      v_4105 <- getRegister v_2452;
      v_4110 <- eval (add (leanSignExtend (extract v_4105 0 16) 32) (leanSignExtend (extract v_4105 16 32) 32));
      v_4120 <- eval (add (leanSignExtend (extract v_4105 32 48) 32) (leanSignExtend (extract v_4105 48 64) 32));
      v_4130 <- eval (add (leanSignExtend (extract v_4105 64 80) 32) (leanSignExtend (extract v_4105 80 96) 32));
      v_4140 <- eval (add (leanSignExtend (extract v_4105 112 128) 32) (leanSignExtend (extract v_4105 96 112) 32));
      setRegister (lhs.of_reg v_2452) (concat (mux (sgt v_4069 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4069 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4069 16 32))) (concat (mux (sgt v_4079 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4079 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4079 16 32))) (concat (mux (sgt v_4089 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4089 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4089 16 32))) (concat (mux (sgt v_4099 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4099 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4099 16 32))) (concat (mux (sgt v_4110 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4110 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4110 16 32))) (concat (mux (sgt v_4120 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4120 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4120 16 32))) (concat (mux (sgt v_4130 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4130 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4130 16 32))) (mux (sgt v_4140 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4140 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4140 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2447 : Mem) (v_2448 : reg (bv 128)) => do
      v_11195 <- evaluateAddress v_2447;
      v_11196 <- load v_11195 16;
      v_11201 <- eval (add (leanSignExtend (extract v_11196 0 16) 32) (leanSignExtend (extract v_11196 16 32) 32));
      v_11211 <- eval (add (leanSignExtend (extract v_11196 32 48) 32) (leanSignExtend (extract v_11196 48 64) 32));
      v_11221 <- eval (add (leanSignExtend (extract v_11196 64 80) 32) (leanSignExtend (extract v_11196 80 96) 32));
      v_11231 <- eval (add (leanSignExtend (extract v_11196 96 112) 32) (leanSignExtend (extract v_11196 112 128) 32));
      v_11237 <- getRegister v_2448;
      v_11242 <- eval (add (leanSignExtend (extract v_11237 0 16) 32) (leanSignExtend (extract v_11237 16 32) 32));
      v_11252 <- eval (add (leanSignExtend (extract v_11237 32 48) 32) (leanSignExtend (extract v_11237 48 64) 32));
      v_11262 <- eval (add (leanSignExtend (extract v_11237 64 80) 32) (leanSignExtend (extract v_11237 80 96) 32));
      v_11272 <- eval (add (leanSignExtend (extract v_11237 112 128) 32) (leanSignExtend (extract v_11237 96 112) 32));
      setRegister (lhs.of_reg v_2448) (concat (mux (sgt v_11201 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11201 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11201 16 32))) (concat (mux (sgt v_11211 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11211 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11211 16 32))) (concat (mux (sgt v_11221 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11221 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11221 16 32))) (concat (mux (sgt v_11231 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11231 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11231 16 32))) (concat (mux (sgt v_11242 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11242 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11242 16 32))) (concat (mux (sgt v_11252 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11252 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11252 16 32))) (concat (mux (sgt v_11262 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11262 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11262 16 32))) (mux (sgt v_11272 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11272 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11272 16 32))))))))));
      pure ()
    pat_end
