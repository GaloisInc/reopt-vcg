def vminps1 : instruction :=
  definst "vminps" $ do
    pattern fun (v_2627 : reg (bv 128)) (v_2628 : reg (bv 128)) (v_2629 : reg (bv 128)) => do
      v_4534 <- getRegister v_2628;
      v_4535 <- eval (extract v_4534 0 32);
      v_4536 <- getRegister v_2627;
      v_4537 <- eval (extract v_4536 0 32);
      v_4541 <- eval (extract v_4534 32 64);
      v_4542 <- eval (extract v_4536 32 64);
      v_4546 <- eval (extract v_4534 64 96);
      v_4547 <- eval (extract v_4536 64 96);
      v_4551 <- eval (extract v_4534 96 128);
      v_4552 <- eval (extract v_4536 96 128);
      setRegister (lhs.of_reg v_2629) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4535 v_4537) (expression.bv_nat 1 1)) v_4535 v_4537) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4541 v_4542) (expression.bv_nat 1 1)) v_4541 v_4542) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4546 v_4547) (expression.bv_nat 1 1)) v_4546 v_4547) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4551 v_4552) (expression.bv_nat 1 1)) v_4551 v_4552))));
      pure ()
    pat_end;
    pattern fun (v_2638 : reg (bv 256)) (v_2639 : reg (bv 256)) (v_2640 : reg (bv 256)) => do
      v_4565 <- getRegister v_2639;
      v_4566 <- eval (extract v_4565 0 32);
      v_4567 <- getRegister v_2638;
      v_4568 <- eval (extract v_4567 0 32);
      v_4572 <- eval (extract v_4565 32 64);
      v_4573 <- eval (extract v_4567 32 64);
      v_4577 <- eval (extract v_4565 64 96);
      v_4578 <- eval (extract v_4567 64 96);
      v_4582 <- eval (extract v_4565 96 128);
      v_4583 <- eval (extract v_4567 96 128);
      v_4587 <- eval (extract v_4565 128 160);
      v_4588 <- eval (extract v_4567 128 160);
      v_4592 <- eval (extract v_4565 160 192);
      v_4593 <- eval (extract v_4567 160 192);
      v_4597 <- eval (extract v_4565 192 224);
      v_4598 <- eval (extract v_4567 192 224);
      v_4602 <- eval (extract v_4565 224 256);
      v_4603 <- eval (extract v_4567 224 256);
      setRegister (lhs.of_reg v_2640) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4566 v_4568) (expression.bv_nat 1 1)) v_4566 v_4568) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4572 v_4573) (expression.bv_nat 1 1)) v_4572 v_4573) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4577 v_4578) (expression.bv_nat 1 1)) v_4577 v_4578) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4582 v_4583) (expression.bv_nat 1 1)) v_4582 v_4583) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4587 v_4588) (expression.bv_nat 1 1)) v_4587 v_4588) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4592 v_4593) (expression.bv_nat 1 1)) v_4592 v_4593) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4597 v_4598) (expression.bv_nat 1 1)) v_4597 v_4598) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_4602 v_4603) (expression.bv_nat 1 1)) v_4602 v_4603))))))));
      pure ()
    pat_end;
    pattern fun (v_2621 : Mem) (v_2622 : reg (bv 128)) (v_2623 : reg (bv 128)) => do
      v_10160 <- getRegister v_2622;
      v_10161 <- eval (extract v_10160 0 32);
      v_10162 <- evaluateAddress v_2621;
      v_10163 <- load v_10162 16;
      v_10164 <- eval (extract v_10163 0 32);
      v_10168 <- eval (extract v_10160 32 64);
      v_10169 <- eval (extract v_10163 32 64);
      v_10173 <- eval (extract v_10160 64 96);
      v_10174 <- eval (extract v_10163 64 96);
      v_10178 <- eval (extract v_10160 96 128);
      v_10179 <- eval (extract v_10163 96 128);
      setRegister (lhs.of_reg v_2623) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10161 v_10164) (expression.bv_nat 1 1)) v_10161 v_10164) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10168 v_10169) (expression.bv_nat 1 1)) v_10168 v_10169) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10173 v_10174) (expression.bv_nat 1 1)) v_10173 v_10174) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10178 v_10179) (expression.bv_nat 1 1)) v_10178 v_10179))));
      pure ()
    pat_end;
    pattern fun (v_2632 : Mem) (v_2633 : reg (bv 256)) (v_2634 : reg (bv 256)) => do
      v_10187 <- getRegister v_2633;
      v_10188 <- eval (extract v_10187 0 32);
      v_10189 <- evaluateAddress v_2632;
      v_10190 <- load v_10189 32;
      v_10191 <- eval (extract v_10190 0 32);
      v_10195 <- eval (extract v_10187 32 64);
      v_10196 <- eval (extract v_10190 32 64);
      v_10200 <- eval (extract v_10187 64 96);
      v_10201 <- eval (extract v_10190 64 96);
      v_10205 <- eval (extract v_10187 96 128);
      v_10206 <- eval (extract v_10190 96 128);
      v_10210 <- eval (extract v_10187 128 160);
      v_10211 <- eval (extract v_10190 128 160);
      v_10215 <- eval (extract v_10187 160 192);
      v_10216 <- eval (extract v_10190 160 192);
      v_10220 <- eval (extract v_10187 192 224);
      v_10221 <- eval (extract v_10190 192 224);
      v_10225 <- eval (extract v_10187 224 256);
      v_10226 <- eval (extract v_10190 224 256);
      setRegister (lhs.of_reg v_2634) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10188 v_10191) (expression.bv_nat 1 1)) v_10188 v_10191) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10195 v_10196) (expression.bv_nat 1 1)) v_10195 v_10196) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10200 v_10201) (expression.bv_nat 1 1)) v_10200 v_10201) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10205 v_10206) (expression.bv_nat 1 1)) v_10205 v_10206) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10210 v_10211) (expression.bv_nat 1 1)) v_10210 v_10211) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10215 v_10216) (expression.bv_nat 1 1)) v_10215 v_10216) (concat (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10220 v_10221) (expression.bv_nat 1 1)) v_10220 v_10221) (mux (eq (_(_,_)_MINT-WRAPPER-SYNTAX mincmp_single v_10225 v_10226) (expression.bv_nat 1 1)) v_10225 v_10226))))))));
      pure ()
    pat_end
