def psadbw1 : instruction :=
  definst "psadbw" $ do
    pattern fun (v_2972 : reg (bv 128)) (v_2973 : reg (bv 128)) => do
      v_6481 <- getRegister v_2973;
      v_6482 <- eval (extract v_6481 0 8);
      v_6483 <- getRegister v_2972;
      v_6484 <- eval (extract v_6483 0 8);
      v_6490 <- eval (extract v_6481 8 16);
      v_6491 <- eval (extract v_6483 8 16);
      v_6497 <- eval (extract v_6481 16 24);
      v_6498 <- eval (extract v_6483 16 24);
      v_6504 <- eval (extract v_6481 24 32);
      v_6505 <- eval (extract v_6483 24 32);
      v_6511 <- eval (extract v_6481 32 40);
      v_6512 <- eval (extract v_6483 32 40);
      v_6518 <- eval (extract v_6481 40 48);
      v_6519 <- eval (extract v_6483 40 48);
      v_6525 <- eval (extract v_6481 48 56);
      v_6526 <- eval (extract v_6483 48 56);
      v_6532 <- eval (extract v_6481 56 64);
      v_6533 <- eval (extract v_6483 56 64);
      v_6546 <- eval (extract v_6481 64 72);
      v_6547 <- eval (extract v_6483 64 72);
      v_6553 <- eval (extract v_6481 72 80);
      v_6554 <- eval (extract v_6483 72 80);
      v_6560 <- eval (extract v_6481 80 88);
      v_6561 <- eval (extract v_6483 80 88);
      v_6567 <- eval (extract v_6481 88 96);
      v_6568 <- eval (extract v_6483 88 96);
      v_6574 <- eval (extract v_6481 96 104);
      v_6575 <- eval (extract v_6483 96 104);
      v_6581 <- eval (extract v_6481 104 112);
      v_6582 <- eval (extract v_6483 104 112);
      v_6588 <- eval (extract v_6481 112 120);
      v_6589 <- eval (extract v_6483 112 120);
      v_6595 <- eval (extract v_6481 120 128);
      v_6596 <- eval (extract v_6483 120 128);
      setRegister (lhs.of_reg v_2973) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_6482 v_6484) (sub v_6482 v_6484) (sub v_6484 v_6482))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6490 v_6491) (sub v_6490 v_6491) (sub v_6491 v_6490))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6497 v_6498) (sub v_6497 v_6498) (sub v_6498 v_6497))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6504 v_6505) (sub v_6504 v_6505) (sub v_6505 v_6504))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6511 v_6512) (sub v_6511 v_6512) (sub v_6512 v_6511))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6518 v_6519) (sub v_6518 v_6519) (sub v_6519 v_6518))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6525 v_6526) (sub v_6525 v_6526) (sub v_6526 v_6525))) (concat (expression.bv_nat 8 0) (mux (ugt v_6532 v_6533) (sub v_6532 v_6533) (sub v_6533 v_6532)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6546 v_6547) (sub v_6546 v_6547) (sub v_6547 v_6546))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6553 v_6554) (sub v_6553 v_6554) (sub v_6554 v_6553))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6560 v_6561) (sub v_6560 v_6561) (sub v_6561 v_6560))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6567 v_6568) (sub v_6567 v_6568) (sub v_6568 v_6567))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6574 v_6575) (sub v_6574 v_6575) (sub v_6575 v_6574))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6581 v_6582) (sub v_6581 v_6582) (sub v_6582 v_6581))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6588 v_6589) (sub v_6588 v_6589) (sub v_6589 v_6588))) (concat (expression.bv_nat 8 0) (mux (ugt v_6595 v_6596) (sub v_6595 v_6596) (sub v_6596 v_6595)))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2968 : Mem) (v_2969 : reg (bv 128)) => do
      v_13161 <- getRegister v_2969;
      v_13162 <- eval (extract v_13161 0 8);
      v_13163 <- evaluateAddress v_2968;
      v_13164 <- load v_13163 16;
      v_13165 <- eval (extract v_13164 0 8);
      v_13171 <- eval (extract v_13161 8 16);
      v_13172 <- eval (extract v_13164 8 16);
      v_13178 <- eval (extract v_13161 16 24);
      v_13179 <- eval (extract v_13164 16 24);
      v_13185 <- eval (extract v_13161 24 32);
      v_13186 <- eval (extract v_13164 24 32);
      v_13192 <- eval (extract v_13161 32 40);
      v_13193 <- eval (extract v_13164 32 40);
      v_13199 <- eval (extract v_13161 40 48);
      v_13200 <- eval (extract v_13164 40 48);
      v_13206 <- eval (extract v_13161 48 56);
      v_13207 <- eval (extract v_13164 48 56);
      v_13213 <- eval (extract v_13161 56 64);
      v_13214 <- eval (extract v_13164 56 64);
      v_13227 <- eval (extract v_13161 64 72);
      v_13228 <- eval (extract v_13164 64 72);
      v_13234 <- eval (extract v_13161 72 80);
      v_13235 <- eval (extract v_13164 72 80);
      v_13241 <- eval (extract v_13161 80 88);
      v_13242 <- eval (extract v_13164 80 88);
      v_13248 <- eval (extract v_13161 88 96);
      v_13249 <- eval (extract v_13164 88 96);
      v_13255 <- eval (extract v_13161 96 104);
      v_13256 <- eval (extract v_13164 96 104);
      v_13262 <- eval (extract v_13161 104 112);
      v_13263 <- eval (extract v_13164 104 112);
      v_13269 <- eval (extract v_13161 112 120);
      v_13270 <- eval (extract v_13164 112 120);
      v_13276 <- eval (extract v_13161 120 128);
      v_13277 <- eval (extract v_13164 120 128);
      setRegister (lhs.of_reg v_2969) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_13162 v_13165) (sub v_13162 v_13165) (sub v_13165 v_13162))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13171 v_13172) (sub v_13171 v_13172) (sub v_13172 v_13171))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13178 v_13179) (sub v_13178 v_13179) (sub v_13179 v_13178))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13185 v_13186) (sub v_13185 v_13186) (sub v_13186 v_13185))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13192 v_13193) (sub v_13192 v_13193) (sub v_13193 v_13192))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13199 v_13200) (sub v_13199 v_13200) (sub v_13200 v_13199))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13206 v_13207) (sub v_13206 v_13207) (sub v_13207 v_13206))) (concat (expression.bv_nat 8 0) (mux (ugt v_13213 v_13214) (sub v_13213 v_13214) (sub v_13214 v_13213)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13227 v_13228) (sub v_13227 v_13228) (sub v_13228 v_13227))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13234 v_13235) (sub v_13234 v_13235) (sub v_13235 v_13234))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13241 v_13242) (sub v_13241 v_13242) (sub v_13242 v_13241))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13248 v_13249) (sub v_13248 v_13249) (sub v_13249 v_13248))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13255 v_13256) (sub v_13255 v_13256) (sub v_13256 v_13255))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13262 v_13263) (sub v_13262 v_13263) (sub v_13263 v_13262))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13269 v_13270) (sub v_13269 v_13270) (sub v_13270 v_13269))) (concat (expression.bv_nat 8 0) (mux (ugt v_13276 v_13277) (sub v_13276 v_13277) (sub v_13277 v_13276)))))))))))));
      pure ()
    pat_end
